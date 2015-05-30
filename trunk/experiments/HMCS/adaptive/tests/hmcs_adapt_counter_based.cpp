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
enum Hysteresis {MOVE_DOWN = -5, STAY_PUT, MOVE_UP = 10};
#endif

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
            HMCSLock<level - 1>::Release(L->parent, &(L->node));
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
        HMCSLock<level - 1>::Release(L->parent, &(L->node));
        COMMIT_ALL_WRITES();
        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        return UNCONTENDED;
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
    bool hasCounterChanged;
    int8_t hysteresis;
    HNode * rootNode;
    bool tookFastPath;
#ifdef HEAVY_WEIGHT_COUNTER
    //NOP
#else
    uint64_t lastSeenAppxCounter;
#endif
    
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
        // Set the root node
        HNode * tmp;
        for(tmp = curNode; tmp->parent != NULL; tmp = tmp->parent);
        rootNode = tmp;
    }
    
    inline void Reset(){
        hysteresis=STAY_PUT;
        curNode=leafNode;
        childNode=NULL;
        curDepth=maxLevels;
        tookFastPath = false;

#ifdef PROFILE
        for(int i = 0 ; i < MAX_STATS; i++)
        stats[i] = 0;
#endif
    }
    
    inline void SignalOnEntry(){
#ifdef HEAVY_WEIGHT_COUNTER
        if ((childNode) && (ATOMIC_ADD(&childNode->contentionCounter, 1) > 0 || childNode->lock))
        haveChildContentionOnEntry = true;
        else
        haveChildContentionOnEntry = false;
#else
        if (childNode) {
            lastSeenAppxCounter =  ATOMIC_ADD(&childNode->appxCounter, 1) + 1;
            haveChildContentionOnEntry = childNode->lock !=  NULL;
        } else {
            haveChildContentionOnEntry = false;
        }
#endif
    }
    
    inline void SignalOnExit(){
#if defined(HEAVY_WEIGHT_COUNTER)
        if ((childNode) && (ATOMIC_ADD(&childNode->contentionCounter, -1) > 1 || childNode->lock))
        haveChildContentionOnExit = true;
        else
        haveChildContentionOnExit = false;
#else
        if (childNode) {
            haveChildContentionOnExit = childNode->lock != NULL;
            hasCounterChanged = lastSeenAppxCounter != childNode->appxCounter;
        } else {
            haveChildContentionOnExit = false;
            hasCounterChanged = false;
        }
#endif
        
    }
    
    
    inline void Acquire(QNode *I){
        
        if(rootNode->lock == NULL) {
            tookFastPath = true;
            HMCSLock<1>::Acquire(rootNode, I);
            return;
        }
        

        
#ifdef PROFILE
        stats[curDepth]++;
#endif
        SignalOnEntry();
        
        switch(curDepth){
            case 1: isUncontendedAcquire = HMCSLock<1>::Acquire(curNode, I); break;
            case 2: isUncontendedAcquire = HMCSLock<2>::Acquire(curNode, I); break;
            case 3: isUncontendedAcquire = HMCSLock<3>::Acquire(curNode, I); break;
            case 4: isUncontendedAcquire = HMCSLock<4>::Acquire(curNode, I); break;
            case 5: isUncontendedAcquire = HMCSLock<5>::Acquire(curNode, I); break;
            default: assert(0 && "NYI");
        }
    }
    
    inline void Release(QNode *I){
        if(tookFastPath) {
            HMCSLock<1>::Release(rootNode, I);
            tookFastPath = false;
            return;
        }
        
        SignalOnExit();
        switch(curDepth){
            case 1: isUncontendedRelease = HMCSLock<1>::Release(curNode, I); break;
            case 2: isUncontendedRelease = HMCSLock<2>::Release(curNode, I); break;
            case 3: isUncontendedRelease = HMCSLock<3>::Release(curNode, I); break;
            case 4: isUncontendedRelease = HMCSLock<4>::Release(curNode, I); break;
            case 5: isUncontendedRelease = HMCSLock<5>::Release(curNode, I); break;
            default: assert(0 && "NYI");
        }
        
#if 1 /* defined(HEAVY_WEIGHT_COUNTER) || defined(APPX_COUNTER) */
        if(childNode && ( (haveChildContentionOnEntry && haveChildContentionOnExit) || hasCounterChanged)){
            hysteresis--;
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
            }
            return;
        }
        if ((curDepth != 1) && (isUncontendedAcquire && isUncontendedRelease)){
            hysteresis++;
            if(hysteresis == MOVE_UP) {
                curDepth--;
                childNode = curNode;
                curNode = curNode->parent;
                //printf("\n UP TO %d\n", curDepth);
                hysteresis = STAY_PUT;
            }
            return;
        }
        
        hysteresis = STAY_PUT;
/*        if(hysteresis > STAY_PUT) {
            hysteresis--;
            return;
        }
        if(hysteresis < STAY_PUT)
        hysteresis ++; */

        //printf("\n STAY PUT %d\n", curDepth);
        // NOT NEEDED .... hysteresis = STAY_PUT;
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


#define LOCKNAME HMCSAdaptiveLock

#include "driver.cpp"
