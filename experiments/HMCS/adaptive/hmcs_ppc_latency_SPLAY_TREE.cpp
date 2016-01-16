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
    uint64_t contentionCounter __attribute__((aligned(CACHE_LINE_SIZE)));
    
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


inline static void NormalMCSReleaseWithValue(HNode * L, QNode *I, uint64_t val){
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
        return;
    }
    if (BOOL_CAS(&(L->lock), I, NULL))
        return;
    while( (succ=I->next) == NULL);
    succ->status = val;
    return;
}

template<int level>
struct HMCSLock{
    inline static void AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            // begining of cohort
            I->status = COHORT_START;
            // Acquire at next level if not at the top level
            HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
            return;
        } else {
            pred->next = I;
            for(;;){
                uint64_t myStatus = I->status;
                if(myStatus < ACQUIRE_PARENT) {
                    return;
                }
                if(myStatus == ACQUIRE_PARENT) {
                    // beginning of cohort
                    I->status = COHORT_START;
                    // This means this level is acquired and we can start the next level
                    HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
                    return;
                }
                // spin back; (I->status == WAIT)
            }
        }
    }
    
    inline static void Acquire(HNode * L, QNode *I) {
        HMCSLock<level>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
    }
    
    
    
    
    
    inline static void ReleaseHelper(HNode * L, QNode *I) {
        
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
            NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
            return;
        }
        
        succ = I->next;
        // Not reached threshold
        if(succ) {
            succ->status = curCount + 1;
            return; // Released
        }
        // No known successor, so release
        HMCSLock<level - 1>::ReleaseHelper(L->parent, &(L->node));
        COMMIT_ALL_WRITES();
        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
    }
    
    inline static void Release(HNode * L, QNode *I) {
        COMMIT_ALL_WRITES();
        HMCSLock<level>::ReleaseHelper(L, I);
    }
};

template <>
struct HMCSLock<1> {
    inline static void AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            return;
        }
        pred->next = I;
        while(I->status==WAIT);
        return;
    }
    
    
    inline static void Acquire(HNode * L, QNode *I) {
        HMCSLock<1>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
    }
    
    inline static void ReleaseHelper(HNode * L, QNode *I) {
        // Top level release is usual MCS
        // At the top level MCS we always writr COHORT_START since
        // 1. It will release the lock
        // 2. Will never grow large
        // 3. Avoids a read from I->status
        NormalMCSReleaseWithValue(L, I, COHORT_START);
    }
    
    inline static void Release(HNode * L, QNode *I) {
        COMMIT_ALL_WRITES();
        HMCSLock<1>::ReleaseHelper(L, I);
    }
    
};

typedef void (*AcquireFP) (HNode *, QNode *);
typedef void (*ReleaseFP) (HNode *, QNode *);
struct HMCSLockWrapper{
    HNode * curNode;
    AcquireFP myAcquire;
    ReleaseFP myRelease;
    int curDepth;
    HMCSLockWrapper(){}
    void ReInit(HNode * h, int depth) {
       curNode=h, curDepth=depth;
        switch(curDepth){
            case 1:  myAcquire = HMCSLock<1>::Acquire; myRelease = HMCSLock<1>::Release; break;
            case 2:  myAcquire = HMCSLock<2>::Acquire; myRelease = HMCSLock<2>::Release; break;
            case 3:  myAcquire = HMCSLock<3>::Acquire; myRelease = HMCSLock<3>::Release; break;
            case 4:  myAcquire = HMCSLock<4>::Acquire; myRelease = HMCSLock<4>::Release; break;
            case 5:  myAcquire = HMCSLock<5>::Acquire; myRelease = HMCSLock<5>::Release; break;
            default: assert(0 && "NYI");
        }
    }
    HMCSLockWrapper(HNode * h, int depth) : curNode(h), curDepth(depth) {
        switch(curDepth){
            case 1:  myAcquire = HMCSLock<1>::Acquire; myRelease = HMCSLock<1>::Release; break;
            case 2:  myAcquire = HMCSLock<2>::Acquire; myRelease = HMCSLock<2>::Release; break;
            case 3:  myAcquire = HMCSLock<3>::Acquire; myRelease = HMCSLock<3>::Release; break;
            case 4:  myAcquire = HMCSLock<4>::Acquire; myRelease = HMCSLock<4>::Release; break;
            case 5:  myAcquire = HMCSLock<5>::Acquire; myRelease = HMCSLock<5>::Release; break;
            default: assert(0 && "NYI");
        }
    }
    inline void Acquire(QNode *I){
        //myAcquire(curNode, I);
        switch(curDepth){
            case 1:  HMCSLock<1>::Acquire(curNode, I); break;
            case 2:  HMCSLock<2>::Acquire(curNode, I); break;
            case 3:  HMCSLock<3>::Acquire(curNode, I); break;
            case 4:  HMCSLock<4>::Acquire(curNode, I); break;
            case 5:  HMCSLock<5>::Acquire(curNode, I); break;
            default: assert(0 && "NYI");
        }
    }
    
    inline void Release(QNode *I){
        //myRelease(curNode, I);
        switch(curDepth){
            case 1:  HMCSLock<1>::Release(curNode, I); break;
            case 2:  HMCSLock<2>::Release(curNode, I); break;
            case 3:  HMCSLock<3>::Release(curNode, I); break;
            case 4:  HMCSLock<4>::Release(curNode, I); break;
            case 5:  HMCSLock<5>::Release(curNode, I); break;
            default: assert(0 && "NYI");
        }
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

void LockInit(HMCSLockWrapper * hmcs, int tid, int maxThreads, int levels, int * participantsAtLevel){
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
            curLock->contentionCounter = 0;
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
    hmcs->ReInit(lockLocations[tid/participantsAtLevel[0]], levels);
    
}

typedef HMCSLockWrapper LockType;

#include "splay_driver.cpp"

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
    
#ifdef COMPUTE_LATENCY
    uint64_t masterTicksSum = 0;
    uint64_t masterIters = 0;
    double * throughPutLatency = new double[numThreads];
#endif
    
#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        uint64_t myIters=0;
        uint64_t numIter = totalIters / numThreads;
#ifdef COMPUTE_LATENCY
        uint64_t myTicksStart = 0;
        uint64_t myTicksEnd = 0;
        uint64_t myTicksSum = 0;
#endif
        struct drand48_data randSeedbuffer;
        srand48_r(tid, &randSeedbuffer);
        
#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif
        HMCSLockWrapper  hmcs;
        LockInit(&hmcs, tid, size, levels, participantsAtLevel);
        
#pragma omp barrier
        // reset myIters
        myIters = 0;
        if(tid % mustBeAMultile !=0)
            goto DONE;
        //printf("\n %d part", tid);
        
        
        if(tid == 0) {
            StartTimer(timeoutSec);
            gettimeofday(&startTime, 0);
        }
        
        myIters = Worker(&hmcs, numIter);
        
#ifdef COMPUTE_LATENCY
        // Compute the thread's Throughput / Latency
        throughPutLatency[tid] =  myIters * myIters * 1.0 / (myTicksSum * myTicksSum);
#endif
        
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
    
#ifdef COMPUTE_LATENCY
    double averageThroughputLatency = 0;
    for(int i = 0 ; i < numThreads; i+=mustBeAMultile){
        averageThroughputLatency += throughPutLatency[i];
    }
    int workingThreads = numThreads / mustBeAMultile;
    averageThroughputLatency = averageThroughputLatency / workingThreads;
    std::cout<<"\n averageThroughputLatency = " << averageThroughputLatency << "\n";
#endif
    return 0;
}

