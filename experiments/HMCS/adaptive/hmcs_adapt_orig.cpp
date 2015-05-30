//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include "util.h"

#include <algorithm>    // std::sort
#include <vector>    // std::sort

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

struct HNode{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct HNode * parent __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode *  volatile lock __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode  node __attribute__((aligned(CACHE_LINE_SIZE)));
    int contentionCounter __attribute__((aligned(CACHE_LINE_SIZE)));
    
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

    inline void SetContentionCounter(int t) {
        contentionCounter = t;
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


typedef bool (*ReleaseFP)(HNode * L, QNode *I);
static ReleaseFP ReleaseLockReal __attribute__((aligned(CACHE_LINE_SIZE)));

enum PassingStatus {UNCONTENDED, CONTENDED};
enum Hysteresis {MOVE_DOWN = -10, STAY_PUT, MOVE_UP = 10};


inline static PassingStatus NormalMCSReleaseWithValue(HNode * L, QNode *I, uint64_t val){
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
        return CONTENDED;
    }
    if (BOOL_CAS(&(L->lock), I, NULL))
        return UNCONTENDED;
    while( (succ=I->next) == NULL);
    succ->status = val;
    return CONTENDED;
}

template<int level>
struct HMCSLock{
    inline static PassingStatus AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            // begining of cohort
            I->status = COHORT_START;
            // Acquire at next level if not at the top level
            HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
            return UNCONTENDED;
        } else {
            pred->next = I;
            for(;;){
                uint64_t myStatus = I->status;
                if(myStatus < ACQUIRE_PARENT) {
                    return CONTENDED;
                }
                if(myStatus == ACQUIRE_PARENT) {
                    // beginning of cohort
                    I->status = COHORT_START;
                    // This means this level is acquired and we can start the next level
                    HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
                    return CONTENDED;
                }
                // spin back; (I->status == WAIT)
            }
        }
    }
    
    inline static PassingStatus Acquire(HNode * L, QNode *I) {
        PassingStatus s = HMCSLock<level>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
        return s;
    }
    
    
    

    
    inline static PassingStatus ReleaseHelper(HNode * L, QNode *I) {
        
        uint64_t curCount = I->status;
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
            // NO KNOWN SUCCESSORS / DESCENDENTS
            // reached threshold and have next level
            // release to next level
            HMCSLock<level - 1>::ReleaseHelper(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            return NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        }
        
        succ = I->next;
        // Not reached threshold
        if(succ) {
            succ->status = curCount + 1;
            return CONTENDED; // Released
        }
        // No known successor, so release
        HMCSLock<level - 1>::ReleaseHelper(L->parent, &(L->node));
        COMMIT_ALL_WRITES();
        // Tap successor at this level and ask to spin acquire next level lock
        return NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
    }
    
    inline static PassingStatus Release(HNode * L, QNode *I) {
        COMMIT_ALL_WRITES();
        return HMCSLock<level>::ReleaseHelper(L, I);
    }
};

template <>
struct HMCSLock<1> {
    inline static PassingStatus AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            return UNCONTENDED;
        }
        pred->next = I;
        while(I->status==WAIT);
        return CONTENDED;
    }
    
    
    inline static PassingStatus Acquire(HNode * L, QNode *I) {
        PassingStatus s = HMCSLock<1>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
        return s;
    }

    inline static PassingStatus ReleaseHelper(HNode * L, QNode *I) {
        // Top level release is usual MCS
        // At the top level MCS we always writr COHORT_START since
        // 1. It will release the lock
        // 2. Will never grow large
        // 3. Avoids a read from I->status
        return NormalMCSReleaseWithValue(L, I, COHORT_START);
    }
    
    inline static PassingStatus Release(HNode * L, QNode *I) {
        COMMIT_ALL_WRITES();
        return HMCSLock<1>::ReleaseHelper(L, I);
    }

};

struct HMCSAdaptiveLock{
    HNode * leafNode;
    HNode * curNode;
    HNode * childNode;
    uint8_t curDepth;
    uint8_t maxLevels;
    bool haveChildContentionOnEntry;
    bool haveChildContentionOnExit;
    bool isUncontendedAcquire;
    bool isUncontendedRelease;
    int8_t hysteresis;
#ifdef PROFILE
#define MAX_STATS (10)
    uint64_t stats[MAX_STATS];
#endif
    
    HMCSAdaptiveLock(HNode * leaf, uint8_t depth) :
        hysteresis(STAY_PUT),
        curNode(leaf), leafNode(leaf), childNode(NULL),
        maxLevels(depth), curDepth(depth),
        isUncontendedAcquire(false), isUncontendedRelease(false), haveChildContentionOnEntry(false), haveChildContentionOnExit(false) {
#ifdef PROFILE
            for(int i = 0 ; i < MAX_STATS; i++)
                stats[i] = 0;
#endif
    }
    
    inline void IncrementChild(){
        if ((childNode) && (ATOMIC_ADD(&childNode->contentionCounter, 1) > 0 || childNode->lock))
            haveChildContentionOnEntry = true;
        else
            haveChildContentionOnEntry = false;
    }
    
    inline void DecrementChild(){
        if ((childNode) && (ATOMIC_ADD(&childNode->contentionCounter, -1) > 1 || childNode->lock))
            haveChildContentionOnExit = true;
        else
            haveChildContentionOnExit = false;
    }

    
    inline void Acquire(QNode *I){
        IncrementChild();

        switch(curDepth){
            case 1: isUncontendedAcquire = HMCSLock<1>::Acquire(curNode, I) == UNCONTENDED; break;
            case 2: isUncontendedAcquire = HMCSLock<2>::Acquire(curNode, I) == UNCONTENDED; break;
            case 3: isUncontendedAcquire = HMCSLock<3>::Acquire(curNode, I) == UNCONTENDED; break;
            case 4: isUncontendedAcquire = HMCSLock<4>::Acquire(curNode, I) == UNCONTENDED; break;
            case 5: isUncontendedAcquire = HMCSLock<5>::Acquire(curNode, I) == UNCONTENDED; break;
            default: assert(0 && "NYI");
        }
        isUncontendedAcquire = isUncontendedAcquire && (curNode->contentionCounter == 0);
#ifdef PROFILE
        stats[curDepth]++;
#endif
    }

    inline void Release(QNode *I){
        switch(curDepth){
            case 1: isUncontendedRelease = HMCSLock<1>::Release(curNode, I) == UNCONTENDED; break;
            case 2: isUncontendedRelease = HMCSLock<2>::Release(curNode, I) == UNCONTENDED; break;
            case 3: isUncontendedRelease = HMCSLock<3>::Release(curNode, I) == UNCONTENDED; break;
            case 4: isUncontendedRelease = HMCSLock<4>::Release(curNode, I) == UNCONTENDED; break;
            case 5: isUncontendedRelease = HMCSLock<5>::Release(curNode, I) == UNCONTENDED; break;
            default: assert(0 && "NYI");
        }
        
        isUncontendedRelease == isUncontendedRelease && (curNode->contentionCounter == 0);
        DecrementChild();
        
        if(childNode && (haveChildContentionOnEntry && haveChildContentionOnExit)){
            if(hysteresis == MOVE_DOWN) {
                curDepth++;
                curNode = childNode;
                if(curDepth == maxLevels) {
                    childNode = NULL;
                } else {
                    HNode * temp;
                    for(temp = leafNode; temp->parent != childNode; temp = temp->parent)
                        ;
                    childNode = temp;
                }
                hysteresis = STAY_PUT;
                //printf("\n DOWN TO %d\n", curDepth);
            } else {
                hysteresis--;
            }
            return;
        }
        if ((curDepth != 1) && (isUncontendedAcquire && isUncontendedRelease)){
            if(hysteresis == MOVE_UP) {
                curDepth--;
                childNode = curNode;
                curNode = curNode->parent;
                //printf("\n UP TO %d\n", curDepth);
                hysteresis = STAY_PUT;
            } else {
                hysteresis++;
            }
            return;
        }
        
        hysteresis = STAY_PUT;
        //printf("\n STAY PUT %d\n", curDepth);
        // NOT NEEDED .... hysteresis = STAY_PUT;
    }
};

/*
 
 8 cores per CPU
 4 CPUs per node
 2 nodes
 ==>
 levels = 3
 participantsAtLevel = {8, 32, 64};
 
 */

HNode ** lockLocations __attribute__((aligned(CACHE_LINE_SIZE)));

HMCSAdaptiveLock * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
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
            curLock->SetContentionCounter(0);
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
    return new HMCSAdaptiveLock(lockLocations[tid/participantsAtLevel[0]], levels);
    
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
hmcs->Acquire(&me); \
CriticalSection();\
hmcs->Release(&me);\
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
    cout<<"\n mustBeAMultile="<<mustBeAMultile <<" timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" numThreads="<<numThreads<<" levels="<<levels<<" ";
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
    
    uint64_t * resultStats1 = new uint64_t[numThreads];
    uint64_t * resultStats2 = new uint64_t[numThreads];
    uint64_t * resultStats3 = new uint64_t[numThreads];
    
    
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
        HMCSAdaptiveLock * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        // Warmup
        QNode me;
        const int warmupRounds = 20;
       // RUN_LOOP(warmupRounds, 10);
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
        
        RUN_LOOP(numIter, 1);
    DONE:
        // If timed out, let us add add total iters executed
        if(gTimedOut){
            ATOMIC_ADD(&totalExecutedIters, myIters);
        }
        
#ifdef PROFILE
// JUST STATUS .. FIX ME
        resultStats1[tid] = hmcs->stats[1];
        resultStats2[tid] = hmcs->stats[2];
        resultStats3[tid] = hmcs->stats[3];
#endif        

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
    
#ifdef PROFILE
    std::vector<uint64_t> myvector1 (resultStats1, resultStats1+numThreads);
    std::sort (myvector1.begin(), myvector1.begin()+numThreads);

    std::vector<uint64_t> myvector2 (resultStats2, resultStats2+numThreads);
    std::sort (myvector2.begin(), myvector2.begin()+numThreads);

    std::vector<uint64_t> myvector3 (resultStats3, resultStats3+numThreads);
    std::sort (myvector3.begin(), myvector3.begin()+numThreads);

    printf("\n 1 = %lu, 2 = %lu, 3 = %lu", myvector1[numThreads/2], myvector2[numThreads/2], myvector3[numThreads/2]);
#endif
    
    elapsed = TIME_SPENT(startTime, endTime);
    double throughPut = (totalExecutedIters) * 1000000.0 / elapsed;
    std::cout<<"\n elapsed = " << elapsed;
    std::cout<<"\n totalExecutedIters = " << totalExecutedIters;
    std::cout<<"\n Throughput = " << throughPut << "\n";
    return 0;
}
