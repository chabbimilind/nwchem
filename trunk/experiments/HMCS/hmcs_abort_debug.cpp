//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include "util.h"

#include <sys/mman.h>
#include <errno.h>
#define PAGE_SIZE (4096)
#define handle_error(msg) \
do { perror(msg); exit(EXIT_FAILURE); } while (0)


struct QNode{
    struct QNode * volatile next __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile uint64_t *status __attribute__((aligned(CACHE_LINE_SIZE)));
    QNode() :  next(NULL) {
        status =  (volatile uint64_t *) memalign(PAGE_SIZE, PAGE_SIZE);
    }
    
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
    
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct HNode{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct HNode * parent __attribute__((aligned(CACHE_LINE_SIZE)));
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


//#define AtomicWrite(var, val) __sync_lock_test_and_set(var, val)

volatile bool gTimedOut __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval startTime __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval endTime __attribute__((aligned(CACHE_LINE_SIZE)));


int threshold;
int * thresholdAtLevel;

inline int GetThresholdAtLevel(int level){
    return thresholdAtLevel[level];
}

static inline void HandleHorizontalAbortion(HNode * L, QNode *I, QNode * abortedNode);


static inline void HandleVerticalAbortion(HNode * L, QNode *I, QNode * abortedNode){
    if(I==abortedNode) {
        return;
    }
#ifdef DEBUG
    assert(AtomicLoad(&(I->status[0])) == COHORT_START);
#endif
    HandleHorizontalAbortion(L, I, abortedNode);
}

static inline void DealWithRestOfHorizontal(HNode * L, QNode *I){
#ifdef DEBUG
    uint64_t oldStatus = AtomicLoad(&(I->status[0])); // TO DO Delete me
#endif
    if(!BOOL_CAS(&(L->lock), I, NULL)) {
        while (I->next == NULL) ; // spin
        uint64_t prevStatus = SWAP(&(I->next->status[0]), ACQUIRE_PARENT);
        if(prevStatus == ABORTED) {
            DealWithRestOfHorizontal(L, I->next);
        }
    }
#ifdef DEBUG
    uint64_t tmp = AtomicLoad(&(I->status[0]));
    assert(tmp == oldStatus || tmp == WAIT /* somebody waiting */ || tmp == ACQUIRE_PARENT /* abort in waiting for READY_TO_USE */);
#endif
    //I->status[0] = READY_TO_USE;
    AtomicWrite(&(I->status[0]),READY_TO_USE);
}

static inline void HandleHorizontalAbortion(HNode * L, QNode *I, QNode * abortedNode){
#ifdef DEBUG
    uint64_t oldStatus = I->status[0]; // TO DO Delete me
#endif
    if (I->next) {
        uint64_t prevStatus = SWAP(&(I->next->status[0]), ACQUIRE_PARENT);
        if(prevStatus == ABORTED){
            HandleHorizontalAbortion(L, I->next, abortedNode);
        }
        
#ifdef DEBUG
        uint64_t tmp = AtomicLoad(&(I->status[0]));
        assert(tmp == oldStatus || tmp == WAIT /* somebody waiting */ || tmp == ACQUIRE_PARENT /* abort in waiting for READY_TO_USE */);
#endif
        //I->status[0] = READY_TO_USE;
        AtomicWrite(&(I->status[0]),READY_TO_USE);
    } else {
        HandleVerticalAbortion(L->parent, &(L->node), abortedNode);
#ifdef DEBUG
        uint64_t tmp = AtomicLoad(&(I->status[0]));
        assert(tmp == oldStatus || tmp == WAIT /* somebody waiting */ || tmp == ACQUIRE_PARENT /* abort in waiting for READY_TO_USE */);
#endif
        // back from vertical abortion
        DealWithRestOfHorizontal(L, I);
    }
}



template<int level>
struct HMCS {
    
    static inline QNode * Acquire(HNode * L, QNode *I, uint64_t patience = UINT64_MAX) {
        // Prepare the node for use.
        
        
        
        uint64_t prevStatus = SWAP(&(I->status[0]), WAIT);
        QNode * pred;
        switch(prevStatus){
            case ABORTED: goto START_SPIN;
            case COHORT_START: goto GOT_LOCK;
            case READY_TO_USE: break;
            case WAIT: break;
            default:
            // Covers case ACQUIRE_PARENT: assert(0 && "CASE ACQUIRE_PARENT");
#ifdef DEBUG
                assert(prevStatus !=  ACQUIRE_PARENT + 1);
#endif
                //while(I->status[0] != READY_TO_USE); No unbounded wait
                for(;patience > 0; patience--) {
                    if(AtomicLoad(&(I->status[0])) == READY_TO_USE){
                        goto USE_QNODE;
                    }
                }
                // Abort
                // TODO .. use CAS
                // Swap with ACQUIRE_PARENT, so that next time when we want to use the node, we go through the default case
                uint64_t statusAtDefaultCase = SWAP(&(I->status[0]), ACQUIRE_PARENT);
                
                if (statusAtDefaultCase != READY_TO_USE) {
#ifdef DEBUG
                    assert(statusAtDefaultCase == WAIT);
#endif
                    // behavior is analogous to an ABORT, except that we don't set status = ABORTED
                    // The predecessor who has walked past me is reponsible for chaning the status to READY_TO_USE
                    return I;
                } // else I is READY_TO_USE fall through to USE_QNODE
                // set I->status[0 back to READY_TO_USE..
                AtomicWrite(&(I->status[0]), READY_TO_USE);
                
        }

    USE_QNODE:
        I->next = NULL;
        // Updates must happen before swap
        COMMIT_ALL_WRITES();
        
        
        pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            // begining of cohort
        GOT_LOCK:
            
            I->status[0] = COHORT_START;

            // Acquire at next level if not at the top level
            //assert(I->status[0] == COHORT_START);
            //printf("\n %p", I->status);
#ifdef DEBUG
            if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                handle_error("mprotect");
#endif
            QNode * ret = HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
#ifdef DEBUG
            if(ret) {
                if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
                    handle_error("mprotect");
            }
#endif
            //assert(I->status[0] == COHORT_START);
            return ret;
        } else {
            pred->next = I;
            
        START_SPIN:
            for(;patience > 0; patience--){
                uint64_t myStatus = AtomicLoad(&(I->status[0])); //I->status[0];
                if(myStatus < ACQUIRE_PARENT) {
#ifdef DEBUG
                    assert(I->status[0] != ACQUIRE_PARENT);
                    if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                        handle_error("mprotect");
#endif
                    return NULL;
                }
                if(myStatus == ACQUIRE_PARENT) {
                    // beginning of cohort
                    I->status[0] = COHORT_START;
#ifdef DEBUG
                    if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                        handle_error("mprotect");
#endif
                    // This means this level is acquired and we can start the next level
                    QNode * ret =  HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
                    
#ifdef DEBUG
                    if(ret) {
                        if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
                            handle_error("mprotect");
                    }
                    assert(I->status[0] == COHORT_START);
#endif
                    return ret;
                }
                // spin back; (I->status[0] == WAIT)
            }
            
            // Abort
            prevStatus = SWAP(&(I->status[0]), ABORTED);
            if(prevStatus < ACQUIRE_PARENT){
                I->status[0] = prevStatus;
#ifdef DEBUG
                assert(I->status[0] != ACQUIRE_PARENT);

                if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                    handle_error("mprotect");
#endif
                return NULL; // got lock;
            }
            if(prevStatus == ACQUIRE_PARENT) {
                I->status[0] = COHORT_START;
#ifdef DEBUG
                if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                    handle_error("mprotect");
#endif
                QNode * ret = HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
#ifdef DEBUG
                if(ret) {
                    if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
                        handle_error("mprotect");
                }
                
                assert(I->status[0] == COHORT_START);
#endif
                return ret;
            } else {
                return I;
            }
        }
    }
    
    static inline bool AcquireWraper(HNode * L, QNode *I, uint64_t patience=UINT64_MAX){
        QNode * abortedNode = HMCS<level>::Acquire(L, I, patience);
        if (abortedNode) {
            HandleVerticalAbortion(L, I, abortedNode);
            return false;
        }
        FORCE_INS_ORDERING();
        return true;
    }

    
    static inline void HandleHorizontalPassing(HNode * L, QNode *I, uint64_t value){
#ifdef DEBUG
        assert(value < ACQUIRE_PARENT);
        uint64_t oldStatus = AtomicLoad(&(I->status[0]));//I->status[0]; // TO DO Delete me
#endif
        if (I->next) {
            uint64_t prevStatus = SWAP(&(I->next->status[0]), value);
            if(prevStatus == ABORTED){
                HandleHorizontalPassing(L, I->next, value);
            }
            
#ifdef DEBUG
            uint64_t tmp = AtomicLoad(&(I->status[0]));
            assert(tmp == oldStatus || tmp == WAIT /* somebody waiting */ || tmp == ACQUIRE_PARENT /* abort in waiting for READY_TO_USE */);
#endif
            //I->status[0] = READY_TO_USE;
            AtomicWrite(&(I->status[0]),READY_TO_USE);
        } else {
            HMCS<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            
#ifdef DEBUG
            uint64_t tmp = AtomicLoad(&(I->status[0]));
            assert(tmp == oldStatus || tmp == WAIT /* somebody waiting */ || tmp == ACQUIRE_PARENT /* abort in waiting for READY_TO_USE */);
#endif
            // Tap successor at this level and ask to spin acquire next level lock
            DealWithRestOfHorizontal(L, I);
        }
    }
    
    
    inline static bool Release(HNode * L, QNode *I) {

        uint64_t curCount = I->status[0];
#ifdef DEBUG
        assert(curCount >= COHORT_START && curCount <= L->GetThreshold());
#endif
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
            HMCS<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
#ifdef DEBUG
            if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
                handle_error("mprotect");
#endif
            // Tap successor at this level and ask to spin acquire next level lock
            DealWithRestOfHorizontal(L, I);
            
            return true; // Released
        }
#ifdef DEBUG
        if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
            handle_error("mprotect");
        assert(curCount < ACQUIRE_PARENT);
#endif
        HandleHorizontalPassing(L, I, curCount + 1);
        return true; // Released
    }
    
};


template <>
struct HMCS<1> {
    
    
    static inline QNode* Acquire(HNode * L, QNode *I, uint64_t patience= UINT64_MAX) {
        // Prepare the node for use.
        uint64_t prevStatus = SWAP(&(I->status[0]), WAIT);

        QNode * pred;
        switch(prevStatus){
            case ABORTED: goto START_SPIN;
            case READY_TO_USE: break;
            case WAIT: break;
            case UNLOCKED:
                //while(I->status[0] != READY_TO_USE); No unbounded wait
                uint64_t statusAtDefaultCase;
                for(;patience > 0; patience--) {
                    if(AtomicLoad(&(I->status[0])) == READY_TO_USE){
                        goto USE_QNODE;
                    }
                }
                // Abort
                // TODO use CAS
                // Swap  UNLOCKED, so that next time when we want to use the node, we go through the UNLOCKED case unless it is updated to READY_TO_USE
                statusAtDefaultCase = SWAP(&(I->status[0]), UNLOCKED);
                
                if (statusAtDefaultCase != READY_TO_USE) {
#ifdef DEBUG
                    assert(statusAtDefaultCase == WAIT);
#endif
                    // behavior is analogous to an ABORT, except that we don't set status = ABORTED
                    // The predecessor who has walked past me is reponsible for chaning the status to READY_TO_USE
                    return I;
                } // else I is READY_TO_USE fall through to USE_QNODE
                // set I->status[0 back to READY_TO_USE..
                AtomicWrite(&(I->status[0]), READY_TO_USE);
                break;
            default:assert(0 && "Should never reach here");
        }
        
    USE_QNODE:
        I->next = NULL;
        // Updates must happen before swap
        COMMIT_ALL_WRITES();
        
        
        pred = (QNode *) SWAP(&(L->lock), I);
        if(pred){
            pred->next = I;
        START_SPIN:
            for(;patience > 0;patience--){
                uint64_t myStatus = I->status[0];
                if(myStatus == UNLOCKED) {
#ifdef DEBUG
                    if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                        handle_error("mprotect");
#endif
                    return NULL; // got lock;
                }
            }
            // Abort
            uint64_t prevStatus = SWAP(&(I->status[0]), ABORTED);
            if(prevStatus == UNLOCKED) {
                I->status[0] = UNLOCKED;
#ifdef DEBUG
                if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
                    handle_error("mprotect");
#endif
                return NULL; // got lock;
            }
            return I;
        } else {
            I->status[0] = UNLOCKED;
        }
        
#ifdef DEBUG
        if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ))
            handle_error("mprotect");
#endif
        return NULL;
    }

    static inline bool AcquireWraper(HNode * L, QNode *I, uint64_t patience=UINT64_MAX){
        QNode * abortedNode = Acquire(L, I, patience);
        if (abortedNode) {
            return false;
        }
        FORCE_INS_ORDERING();
        return true;
    }

    static inline void DealWithRestOfLevel1(HNode * L, QNode *I){
        if(!BOOL_CAS(&(L->lock), I, NULL)) {
            while (I->next == NULL) ; // spin
            uint64_t prevStatus = SWAP(&(I->next->status[0]), UNLOCKED);
            if(prevStatus == ABORTED) {
                DealWithRestOfLevel1(L, I->next);
            }
        }
        // Reset status
        //I->status[0] = READY_TO_USE;
        AtomicWrite(&(I->status[0]),READY_TO_USE);
    }
    
    static inline void HandleHorizontalPassing(HNode * L, QNode *I){
        if (I->next) {
            uint64_t prevStatus = SWAP(&(I->next->status[0]), UNLOCKED);
            if(prevStatus == ABORTED){
                HandleHorizontalPassing(L, I->next);
            }
            // Reset status
            //I->status[0] = READY_TO_USE;
            AtomicWrite(&(I->status[0]),READY_TO_USE);
        } else {
            DealWithRestOfLevel1(L, I);
        }
    }
    
    
    inline static bool Release(HNode * L, QNode *I) {
#ifdef DEBUG
        assert(I->status[0] == UNLOCKED);
        if(mprotect((void*)(I->status), PAGE_SIZE, PROT_READ|PROT_WRITE))
            handle_error("mprotect");
#endif
        HandleHorizontalPassing(L, I);
        return true;
    }
};

#define ReleaseWrapper(L, I, level) do{\
    COMMIT_ALL_WRITES();\
    HMCS<level>::Release(L, I); }while(0)

/*
 
 8 cores per CPU
 4 CPUs per node
 2 nodes
 ==>
 levels = 3
 participantsAtLevel = {8, 32, 64};
 
 */

HNode ** lockLocations __attribute__((aligned(CACHE_LINE_SIZE)));

HNode * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1
    
    int totalLocksNeeded = 0;
    for (int i=0; i < levels; i++) {
        totalLocksNeeded += maxThreads / participantsAtLevel[i] ;
    }
#pragma omp single
    {
        //lockLocations = new HNode*[totalLocksNeeded];
        // use memalign for alignemnt new does not ensure alignment
        lockLocations = (HNode**)memalign(CACHE_LINE_SIZE, sizeof(HNode*) * totalLocksNeeded);
    }
    
    // Lock at curLevel l will be initialized by a designated master
    
    int lastLockLocationEnd = 0;
    for(int curLevel = 0 ; curLevel < levels; curLevel++){
        if (tid%participantsAtLevel[curLevel] == 0) {
            // master, initialize the lock
            int lockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel];
            lastLockLocationEnd += maxThreads/participantsAtLevel[curLevel];
            HNode * curLock = new HNode();
            curLock->threshold = GetThresholdAtLevel(curLevel);
            curLock->parent = NULL;
            curLock->node.status[0] = WAIT;
            curLock->node.next = NULL;
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
    HNode * leafHNode = new HNode();
    leafHNode->parent = lockLocations[tid/participantsAtLevel[0]];
    leafHNode->lock = 0; // never used.
    leafHNode->node.status[0] = WAIT;
    leafHNode->node.next = NULL;

    return leafHNode;
    
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
                                    if (HMCS<level>::AcquireWraper(hmcs->parent, &(hmcs->node)) == true ) { \
                                    CriticalSection();\
                                    ReleaseWrapper(hmcs->parent, &(hmcs->node), level);}\
                                    OutsideCriticalSection(& randSeedbuffer);\
                              }}while(0)

using namespace std;
int main(int argc, char *argv[]){
    
    uint64_t timeoutSec = atol(argv[1]);
    uint64_t totalIters = atol(argv[2]);
    int numThreads = atoi(argv[3]);
    int levels = atoi(argv[4]);
    int * participantsAtLevel = (int * ) malloc(sizeof(int) * levels);
    thresholdAtLevel = (int * ) malloc(sizeof(int) * levels);
    cout<<"\n timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" numThreads="<<numThreads<<" levels="<<levels<<" ";
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[5 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[5 + 2*i + 1]);
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
        HNode * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        // Warmup
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
            case 9:
                RUN_LOOP(warmupRounds, 9);
                break;
            case 10:
                RUN_LOOP(warmupRounds, 10);
                break;
            default:
                assert(0 && "ReleaseWrapper > 10 NYI" );
                break;
        }
#pragma omp barrier
        
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
            case 9:
                RUN_LOOP(numIter, 9);
                break;
            case 10:
                RUN_LOOP(numIter, 10);
                break;
            default:
                assert(0 && "ReleaseWrapper > 10 NYI" );
                break;
        }
        // If timed out, let us add add total iters executed
        if(gTimedOut){
            ATOMIC_ADD(&totalExecutedIters, myIters);
        }
    }
    
    // If not timed out, let us get the end time and total iters
    if(!gTimedOut){
        gettimeofday(&endTime, 0);
        totalExecutedIters = (totalIters / numThreads) * numThreads;
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


