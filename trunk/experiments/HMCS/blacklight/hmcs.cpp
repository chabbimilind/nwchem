//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include "util.h"

struct QNode{
    struct QNode * volatile next __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile uint64_t status __attribute__((aligned(CACHE_LINE_SIZE)));
    QNode() : status(WAIT), next(NULL) {
        
    }
    
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
    
    
    inline void Reuse(){
        status = WAIT;
        next = NULL;
        // Updates must happen before swap
        COMMIT_ALL_WRITES();
    }
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct HMCS{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct HMCS * parent __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode *  volatile lock __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode  node __attribute__((aligned(CACHE_LINE_SIZE)));
    
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
    
    inline bool IsTopLevel() {
        return parent == NULL ? true : false;
    }
    
    inline uint64_t GetThreshold()const {
        return threshold;
    }
    
    inline void SetThreshold(uint64_t t) {
        threshold = t;
    }
    
    
}__attribute__((aligned(CACHE_LINE_SIZE)));



volatile bool gTimedOut __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval startTime __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval endTime __attribute__((aligned(CACHE_LINE_SIZE)));


int threshold;
int * thresholdAtLevel;

inline int GetThresholdAtLevel(int level){
    return thresholdAtLevel[level];
}


typedef bool (*ReleaseFP)(HMCS * L, QNode *I);
static ReleaseFP ReleaseLockReal __attribute__((aligned(CACHE_LINE_SIZE)));

static void Acquire(HMCS * L, QNode *I);
static inline void AcquireParent(HMCS * L) {
    Acquire(L->parent, &(L->node));
}

#define ACQUIRE_NEXT_LEVEL_MCS_LOCK(L) do{I=&(L->node); L=L->parent; goto START;} while(0)

static inline void Acquire(HMCS * L, QNode *I) {
START:
    // Prepare the node for use.
    I->Reuse();
    QNode * pred = (QNode *) SWAP(&(L->lock), I);
    if(!pred) {
        // I am the first one at this level
        // begining of cohort
        I->status = COHORT_START;
        // Acquire at next level if not at the top level
        if(!(L->IsTopLevel())) {
            // This means this level is acquired and we can start the next level
            ACQUIRE_NEXT_LEVEL_MCS_LOCK(L);
        }
    } else {
        pred->next = I;
        for(;;){
            uint64_t myStatus = I->status;
            if(myStatus < ACQUIRE_PARENT) {
                break;
            }
            if(myStatus == ACQUIRE_PARENT) {
                // beginning of cohort
                I->status = COHORT_START;
                // This means this level is acquired and we can start the next level
                ACQUIRE_NEXT_LEVEL_MCS_LOCK(L);
                break;
            }
            // spin back; (I->status == WAIT)
        }
    }
}

#define AcquireWraper(L, I) do {\
    Acquire(L, I);\
    FORCE_INS_ORDERING(); }while(0)

inline static void NormalMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
    } else {
        if (BOOL_CAS(&(L->lock), I, NULL))
            return;
        while( (succ=I->next) == NULL);
        succ->status = val;
    }
}

inline static  bool TryMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
        return true;
    } else {
        // found no successor so, did not release
        return false;
    }
}




template<int level>
struct LockRelease {
    inline static bool Release(HMCS * L, QNode *I
#ifdef TRY_RELEASE
, bool tryRelease=false
#endif
) {

        uint64_t curCount = I->status;
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
#ifdef TRY_RELEASE
            succ  = I->next;
            // if I have successors, we'll try release
            if( tryRelease || succ) {
                bool releaseVal = LockRelease<level - 1>::Release(L->parent, &(L->node), true /* try release */);
                if(releaseVal){
                    COMMIT_ALL_WRITES();
                    // Tap successor at this level and ask to spin acquire next level lock
                    NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
                    return true; // released
                }
                // retaining lock
                // if tryRelease == true, pass it to descendents
                if (tryRelease) {
                    return false; // not released
                }
                // pass it to peers
                // Tap successor at this level
                succ->status=  COHORT_START; /* give one full chunk */
                return true; //released
            }
#endif            
            // NO KNOWN SUCCESSORS / DESCENDENTS
            // reached threshold and have next level
            // release to next level
            LockRelease<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
            return true; // Released
        }
        
        succ = I->next;
        // Not reached threshold
        if(succ) {
            succ->status = curCount + 1;
            return true; // Released
        } else {
            // No known successor, so release
            LockRelease<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
            return true; // Released
        }
    }
    
};

template <>
struct LockRelease<1> {
    inline static bool Release(HMCS * L, QNode *I
#ifdef TRY_RELEASE
, bool tryRelease=false
#endif
) {
        // Top level release is usual MCS
        // At the top level MCS we always writr COHORT_START since
        // 1. It will release the lock
        // 2. Will never grow large
        // 3. Avoids a read from I->status
#ifdef TRY_RELEASE
        if(tryRelease) {
            bool retVal = TryMCSReleaseWithValue(L, I, COHORT_START);
            return retVal;
        }
#endif
        NormalMCSReleaseWithValue(L, I, COHORT_START);
        return true;
    }
};

#define ReleaseWrapper(L, I, level) do{\
    COMMIT_ALL_WRITES();\
    LockRelease<level>::Release(L, I); }while(0)

/*
 
 8 cores per CPU
 4 CPUs per node
 2 nodes
 ==>
 levels = 3
 participantsAtLevel = {8, 32, 64};
 
 */

HMCS ** lockLocations __attribute__((aligned(CACHE_LINE_SIZE)));

HMCS * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1
    
    
#pragma omp single
    {
        switch (levels) {
            case 1:
                ReleaseLockReal = LockRelease<1>::Release;
                break;
            case 2:
                ReleaseLockReal = LockRelease<2>::Release;
                break;
            case 3:
                ReleaseLockReal = LockRelease<3>::Release;
                break;
            case 4:
                ReleaseLockReal = LockRelease<4>::Release;
                break;
            case 5:
                ReleaseLockReal = LockRelease<5>::Release;
                break;
            case 6:
                ReleaseLockReal = LockRelease<6>::Release;
                break;
            case 7:
                ReleaseLockReal = LockRelease<7>::Release;
                break;
            case 8:
                ReleaseLockReal = LockRelease<8>::Release;
                break;
            default:
                assert(0 && "Release > 8 NYI");
                break;
        }
    }
    
    int totalLocksNeeded = 0;
    for (int i=0; i < levels; i++) {
        totalLocksNeeded += maxThreads / participantsAtLevel[i] ;
    }
#pragma omp single
    {
        //lockLocations = new HMCS*[totalLocksNeeded];
        // use memalign for alignemnt new does not ensure alignment
        lockLocations = (HMCS**)memalign(CACHE_LINE_SIZE, sizeof(HMCS*) * totalLocksNeeded);
    }
    
    // Lock at curLevel l will be initialized by a designated master
    
    int lastLockLocationEnd = 0;
    for(int curLevel = 0 ; curLevel < levels; curLevel++){
        if (tid%participantsAtLevel[curLevel] == 0) {
            // master, initialize the lock
            int lockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel];
            lastLockLocationEnd += maxThreads/participantsAtLevel[curLevel];
            HMCS * curLock = new HMCS();
            curLock->threshold = GetThresholdAtLevel(curLevel);
            curLock->parent = NULL;
            //curLock->node = NULL;
            //curLock->node = new QNode();
            curLock->lock = NULL;
            lockLocations[lockLocation] = curLock;
            
        }
    }
#pragma omp barrier
    // setup parents
    lastLockLocationEnd = 0;
    for(int curLevel = 0 ; curLevel < levels - 1; curLevel++){
        if (tid%participantsAtLevel[curLevel] == 0) {
            // master, initialize the lock
            int lockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel];
            lastLockLocationEnd += maxThreads/participantsAtLevel[curLevel];
            int parentLockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel+1];
            lockLocations[lockLocation]->parent = lockLocations[parentLockLocation];
        }
    }
#pragma omp barrier
    // return the lock to each thread
    return lockLocations[tid/participantsAtLevel[0]];
    
}


void AlarmHandler(int sig) {
    printf("\n Time out!\n");
    exit(-1);
}


static inline void CriticalSection(){
#ifdef  DOWORK
    DoWorkInsideCS();
#endif
    
#ifdef VALIDATE
    int lvar = var;
    var ++;
    assert(var == lvar + 1);
#endif
}
static inline void OutsideCriticalSection(struct drand48_data * randSeedbuffer){
#ifdef  DOWORK
    DoWorkOutsideCS(randSeedbuffer);
#endif
}

struct sigevent gSev;
timer_t gTimerid;
#define REALTIME_SIGNAL       (SIGRTMIN + 3)
#define errExit(msg)    do { perror(msg); exit(EXIT_FAILURE);} while (0)

void StartTimer(uint64_t timeoutSec){
    struct itimerspec its;
    /* Start the timer */
    its.it_value.tv_sec = timeoutSec;
    its.it_value.tv_nsec = 0;
    its.it_interval.tv_sec = 0;
    its.it_interval.tv_nsec = 0;
    
    if (timer_settime(gTimerid, 0, &its, NULL) == -1)
        errExit("timer_settime");
}

static void TimeoutHandler(int sig, siginfo_t* siginfo, void* p){
    // Stop timer and tell all threads to quit.
    gTimedOut = true;
    COMMIT_ALL_WRITES();
    gettimeofday(&endTime, 0);
}

static void CreateTimer(){
    
    // the man pages cite sigev_notify_thread_id in struct sigevent,
    // but often the only name is a hidden union name.
#ifndef sigev_notify_thread_id
#define sigev_notify_thread_id  _sigev_un._tid
#endif
    
    memset(&gSev, 0, sizeof(struct sigevent));
    gSev.sigev_notify = SIGEV_THREAD_ID;
    gSev.sigev_signo = REALTIME_SIGNAL;
    gSev.sigev_value.sival_ptr = &gTimerid;
    gSev.sigev_notify_thread_id = syscall(SYS_gettid);
    clockid_t clock = CLOCK_REALTIME;
    int ret = timer_create(clock, &gSev, &gTimerid);
    assert(ret == 0);
    
    /* Establish handler for timer signal */
    //printf("Establishing handler for signal %d\n", REALTIME_SIGNAL);
    struct sigaction sa;
    sa.sa_flags = SA_SIGINFO;
    sa.sa_sigaction = TimeoutHandler;
    sigemptyset(&sa.sa_mask);
    if (sigaction(REALTIME_SIGNAL, &sa, NULL) == -1)
        errExit("sigaction");
}

#define RUN_LOOP(nIter, level)       do{for(myIters = 0; (myIters < nIter) && (!gTimedOut); myIters++) { \
                                    AcquireWraper(hmcs, &me); \
                                    CriticalSection();\
                                    ReleaseWrapper(hmcs, &me, level);\
                                    OutsideCriticalSection(& randSeedbuffer);\
                              }}while(0)

using namespace std;
int main(int argc, char *argv[]){
    
    uint64_t mustBeAMultile = atol(argv[1]);
    uint64_t timeoutSec = atol(argv[2]);
    uint64_t totalIters = atol(argv[3]);
    int numThreads = atoi(argv[4]);
    int levels = atoi(argv[5]);
    int * participantsAtLevel = (int * ) malloc(sizeof(int) * levels);
    thresholdAtLevel = (int * ) malloc(sizeof(int) * levels);
    cout<<"\n timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" numThreads="<<numThreads<<" levels="<<levels<<" ";
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[6 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[6 + 2*i + 1]);
	cout<<" n"<<i+1<<"="<<participantsAtLevel[i]<<" t"<<i+1<<"="<<thresholdAtLevel[i];
    }
    cout<<endl; 

    
    // initalize
    gTimedOut = false;
    
    omp_set_num_threads(numThreads);
    uint64_t elapsed;
    uint64_t totalExecutedIters = 0;
    
    // Set up alarm after 3 minutes to time out
    //signal(SIGALRM, AlarmHandler);
    //alarm(ALARM_TIME);
    CreateTimer();
    
#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        uint64_t myIters=0;
        uint64_t numIter = totalIters / numThreads;
        struct drand48_data randSeedbuffer;
        srand48_r(tid, &randSeedbuffer);
        
#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif
        HMCS * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        // Warmup
        QNode me;
        const int warmupRounds = 20;
        switch (levels) {
            case 1:
                RUN_LOOP(warmupRounds, 1);
                break;
            case 2:
                RUN_LOOP(warmupRounds, 2);
                break;
            case 3:
                RUN_LOOP(warmupRounds, 3);
                break;
            case 4:
                RUN_LOOP(warmupRounds, 4);
                break;
            case 5:
                RUN_LOOP(warmupRounds, 5);
                break;
            case 6:
                RUN_LOOP(warmupRounds, 6);
                break;
            case 7:
                RUN_LOOP(warmupRounds, 7);
                break;
            case 8:
                RUN_LOOP(warmupRounds, 8);
                break;
            default:
                assert(0 && "ReleaseWrapper > 8 NYI" );
                break;
        }
#pragma omp barrier
        // rest myIters
        myIters = 0; 
        if(tid % mustBeAMultile !=0)
            goto DONE;
	//printf("\n %d part", tid);

        if(tid == 0) {
            StartTimer(timeoutSec);
            gettimeofday(&startTime, 0);
        }
        
        switch (levels) {
            case 1:
                RUN_LOOP(numIter, 1);
                break;
            case 2:
                RUN_LOOP(numIter, 2);
                break;
            case 3:
                RUN_LOOP(numIter, 3);
                break;
            case 4:
                RUN_LOOP(numIter, 4);
                break;
            case 5:
                RUN_LOOP(numIter, 5);
                break;
            case 6:
                RUN_LOOP(numIter, 6);
                break;
            case 7:
                RUN_LOOP(numIter, 7);
                break;
            case 8:
                RUN_LOOP(numIter, 8);
                break;
            default:
                assert(0 && "ReleaseWrapper > 8 NYI" );
                break;
        }
DONE:
        // If timed out, let us add add total iters executed
        if(gTimedOut){
            ATOMIC_ADD(&totalExecutedIters, myIters);
        }
    }
    
    // If not timed out, let us get the end time and total iters
    if(!gTimedOut){
        gettimeofday(&endTime, 0);
        totalExecutedIters = (totalIters / numThreads) * (numThreads/mustBeAMultile);
    } else {
      std::cout<<"\n Timed out";
      // All except thread 0 (signal received) will report 1 trip extra
      // If each thread performs 1K iters, it is a small .1% skid. So ignore.
    }
    
    elapsed = TIME_SPENT(startTime, endTime);
    double throughPut = (totalExecutedIters) * 1000000.0 / elapsed;
    std::cout<<"\n elapsed = " << elapsed;
    std::cout<<"\n totalExecutedIters = " << totalExecutedIters;
    std::cout<<"\n Throughput = " << throughPut << "\n";
    return 0;
}

