//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include "util.h"

#include <algorithm>    // std::sort
#include <vector>    // std::sort

#ifdef USE_TSX
#include <immintrin.h>
#define END_TSX() _xend()
#define ABORT_TSX(a) _xabort(a)
#define BEGIN_TSX(a) _xbegin()
#endif

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
    
    
#if defined(HEAVY_WEIGHT_COUNTER)
    int contentionCounter __attribute__((aligned(CACHE_LINE_SIZE)));
#else // assume defined(APPX_COUNTER)
    uint64_t appxCounter __attribute__((aligned(CACHE_LINE_SIZE)));
#endif
    
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
    
#if defined(HEAVY_WEIGHT_COUNTER)
    inline void SetContentionCounter(int t) {
        contentionCounter = t;
    }
#else // assume defined(APPX_COUNTER)
    inline void SetContentionCounter(uint64_t t) {
        appxCounter = t;
    }
#endif
    
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

enum PassingStatus {UNCONTENDED=true, CONTENDED=false};
#ifdef HEAVY_WEIGHT_COUNTER
enum Hysteresis {MOVE_DOWN = -10, STAY_PUT, MOVE_UP = 10};
#else // assume defined(APPX_COUNTER)
enum Hysteresis {MOVE_DOWN = -20, STAY_PUT, MOVE_UP = 20};
#endif

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
    inline static int AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            // begining of cohort
            I->status = COHORT_START;
            // Acquire at next level if not at the top level
            return HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
        } else {
            pred->next = I;
            for(;;){
                uint64_t myStatus = I->status;
                if(myStatus < ACQUIRE_PARENT) {
                    return level;
                }
                if(myStatus == ACQUIRE_PARENT) {
                    // beginning of cohort
                    I->status = COHORT_START;
                    // This means this level is acquired and we can start the next level
                    HMCSLock<level-1>::AcquireHelper(L->parent, &(L->node));
                    return level;
                }
                // spin back; (I->status == WAIT)
            }
        }
    }
    
    inline static int Acquire(HNode * L, QNode *I) {
        int s = HMCSLock<level>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
        return s;
    }
    
    
    
    
    
    inline static int ReleaseHelper(HNode * L, QNode *I) {
        
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
            // if we passed many times, we can simply say this one would have found a successor as well
            return level;
        }
        
        succ = I->next;
        // Not reached threshold
        if(succ) {
            succ->status = curCount + 1;
            return level; // Released
        }
        // No known successor, so release
        int whereReleased = HMCSLock<level - 1>::ReleaseHelper(L->parent, &(L->node));
        COMMIT_ALL_WRITES();
        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        return whereReleased;
    }
    
    inline static int Release(HNode * L, QNode *I) {
        COMMIT_ALL_WRITES();
        return HMCSLock<level>::ReleaseHelper(L, I);
    }
};

template <>
struct HMCSLock<1> {
    inline static int AcquireHelper(HNode * L, QNode *I) {
        // Prepare the node for use.
        I->Reuse();
        QNode * pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            return 1;
        }
        pred->next = I;
        while(I->status==WAIT);
        return 1;
    }
    
    
    inline static int Acquire(HNode * L, QNode *I) {
        int s = HMCSLock<1>::AcquireHelper(L, I);
        FORCE_INS_ORDERING();
        return s;
    }
    
    inline static int ReleaseHelper(HNode * L, QNode *I) {
        // Top level release is usual MCS
        // At the top level MCS we always writr COHORT_START since
        // 1. It will release the lock
        // 2. Will never grow large
        // 3. Avoids a read from I->status
        NormalMCSReleaseWithValue(L, I, COHORT_START);
        return 1;
    }
    
    inline static int Release(HNode * L, QNode *I) {
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
    int8_t hysteresis;
    int depthToEnqueue;
    HNode * nodeToEnqueue;
    int depthFirstWaited;
    int depthlFirstPassed;
    HNode * rootNode;
    bool tookFastPath;
    
#ifdef PROFILE
#define MAX_STATS (10)
    uint64_t stats[MAX_STATS];
#endif
    
    HMCSAdaptiveLock(){}

    HMCSAdaptiveLock(HNode * leaf, uint8_t depth) :
    hysteresis(STAY_PUT),
    curNode(leaf), leafNode(leaf), childNode(NULL), depthToEnqueue(depth), nodeToEnqueue(leaf),
    maxLevels(depth), curDepth(depth), tookFastPath(false)
    {
#ifdef PROFILE
        for(int i = 0 ; i < MAX_STATS; i++)
        stats[i] = 0;
#endif
        // Set the root node
        HNode * tmp;
        for(tmp = curNode; tmp->parent != NULL; tmp = tmp->parent);
        rootNode = tmp;
    }
    void ReInit(HNode * leaf, uint8_t depth){
    hysteresis=STAY_PUT,
    curNode=leaf, leafNode=leaf, childNode=NULL, depthToEnqueue=depth, nodeToEnqueue=leaf,
    maxLevels=depth, curDepth=depth, tookFastPath=false;
#ifdef PROFILE
        for(int i = 0 ; i < MAX_STATS; i++)
        stats[i] = 0;
#endif
        // Set the root node
        HNode * tmp;
        for(tmp = curNode; tmp->parent != NULL; tmp = tmp->parent);
        rootNode = tmp;
    }
    
    void Reset(){
        hysteresis=STAY_PUT;
        curNode=leafNode;
        childNode=NULL;
        curDepth=maxLevels;
        tookFastPath = false;
        depthToEnqueue = maxLevels;
        nodeToEnqueue = leafNode;
#ifdef PROFILE
        for(int i = 0 ; i < MAX_STATS; i++)
        stats[i] = 0;
#endif
    }
    
    
    inline void Acquire(QNode *I){

        // Fast path ... If root is null, enqueue there
        //if(nodeToEnqueue->lock == NULL && rootNode->lock == NULL) {
        QNode * curTail;
	if( (curTail=curNode->lock) == NULL){
#ifdef USE_TSX

		// avoid lemming effect
			int statusTsx;
#ifdef AVOID_LEMMING_EFFECT
		for(int retryCnt = 0 ; retryCnt < 5; retryCnt++) {
			while(rootNode->lock != NULL ) /* spin */ ; // wait for the lock to be free
#endif //end AVOID_LEMMING_EFFECT
			if( (statusTsx=BEGIN_TSX(tmBuf)) == _XBEGIN_STARTED) {
#endif // end USE_TSX
				if(rootNode->lock == NULL){
#ifdef PROFILE
					stats[1]++;
#endif // end PROFILE
					tookFastPath = true;
#ifndef USE_TSX
					HMCSLock<1>::Acquire(rootNode, I);
#endif //end USE_TSX
					return;
				}
#ifdef USE_TSX
				else {
					ABORT_TSX(0xff); // lock busy
				}
			}
#if  defined(AVOID_LEMMING_EFFECT) && defined(USE_TSX)
			if ((statusTsx & _XABORT_EXPLICIT) && 
					_XABORT_CODE(statusTsx) == 0xff) {
				//Wait for lock to become free
				while(rootNode->lock != NULL ) /* spin */ ; // wait for the lock to be free
			} else if (!(statusTsx & _XABORT_RETRY))
				break;
		}// end for
#endif //end defined(AVOID_LEMMING_EFFECT) && defined(USE_TSX)

#endif // end USE_TSX
		depthToEnqueue = curDepth;
		nodeToEnqueue = curNode;
	} else if(childNode && (I->next != curTail)){
		depthToEnqueue = curDepth + 1;
		nodeToEnqueue = childNode;
	} else {
		depthToEnqueue = curDepth;
		nodeToEnqueue = curNode;
	}

#ifdef PROFILE
        stats[depthToEnqueue]++;
#endif

// avoid lemming effect
#if  defined(AVOID_LEMMING_EFFECT) && defined(USE_TSX)
            while((curNode->lock==NULL) && (rootNode->lock != NULL)) /*spin*/ ; // wait if root is held and curNode is not held
#endif
        switch(depthToEnqueue){
            case 1: depthFirstWaited = HMCSLock<1>::Acquire(nodeToEnqueue, I); break;
            case 2: depthFirstWaited = HMCSLock<2>::Acquire(nodeToEnqueue, I); break;
            case 3: depthFirstWaited = HMCSLock<3>::Acquire(nodeToEnqueue, I); break;
            case 4: depthFirstWaited = HMCSLock<4>::Acquire(nodeToEnqueue, I); break;
            case 5: depthFirstWaited = HMCSLock<5>::Acquire(nodeToEnqueue, I); break;
            default: assert(0 && "NYI");
        }
    }
    
    inline void Release(QNode *I){
        if(tookFastPath) {
#ifdef USE_TSX
            END_TSX();
#else
            HMCSLock<1>::Release(rootNode, I);
#endif
            tookFastPath = false;
            return;
        }

        switch(depthToEnqueue){
            case 1: depthlFirstPassed = HMCSLock<1>::Release(nodeToEnqueue, I); break;
            case 2: depthlFirstPassed = HMCSLock<2>::Release(nodeToEnqueue, I); break;
            case 3: depthlFirstPassed = HMCSLock<3>::Release(nodeToEnqueue, I); break;
            case 4: depthlFirstPassed = HMCSLock<4>::Release(nodeToEnqueue, I); break;
            case 5: depthlFirstPassed = HMCSLock<5>::Release(nodeToEnqueue, I); break;
            default: assert(0 && "NYI");
        }

#if 1 /* defined(HEAVY_WEIGHT_COUNTER) || defined(APPX_COUNTER) */
        if(childNode && ( (depthFirstWaited > curDepth) || (depthlFirstPassed > curDepth)) ){
            curDepth++;
            curNode = childNode;
            if(curDepth == maxLevels) {
                childNode = NULL;
                return;
            }
            
            //else {
            HNode * temp;
            for(temp = leafNode; temp->parent != childNode; temp = temp->parent)
            ;
            childNode = temp;
            return;
        }
        if ((curDepth != 1) && ( (depthFirstWaited <  curDepth) && (depthlFirstPassed < curDepth))){
            curDepth--;
            childNode = curNode;
            curNode = curNode->parent;
            return;
        }
        
#else
        assert(0);
#endif
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

void LockInit(HMCSAdaptiveLock * ahmcs, int tid, int maxThreads, int levels, int * participantsAtLevel){
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
    ahmcs->ReInit(lockLocations[tid/participantsAtLevel[0]], levels);
    
}


typedef HMCSAdaptiveLock LockType;
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
    
#ifdef PROFILE
    // FIX ME.. JUST FOR 3 level lock to get stats
    uint64_t * resultStats1 = new uint64_t[numThreads];
    uint64_t * resultStats2 = new uint64_t[numThreads];
    uint64_t * resultStats3 = new uint64_t[numThreads];
#endif
    
#ifdef COMPUTE_LATENCY
    uint64_t masterTicksSum = 0;
    uint64_t masterIters = 0;
    double * throughPutLatency = new double[numThreads];
#endif
    Populate(MAX_SPLAY_TREE_KEYS);

 
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
        HMCSAdaptiveLock  hmcs;
        LockInit(&hmcs,tid, size, levels, participantsAtLevel);
        
        hmcs.Reset();
#ifdef COMPUTE_LATENCY
        myTicksStart = 0;
        myTicksEnd = 0;
        myTicksSum = 0;
#endif
        
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
    printf("\n 1 = %lu, 2 = %lu, 3 = %lu", resultStats1[0], resultStats2[0], resultStats3[0]);
#endif
    
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

