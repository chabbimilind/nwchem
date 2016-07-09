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
    volatile uint64_t status __attribute__((aligned(CACHE_LINE_SIZE)));
    char buf[CACHE_LINE_SIZE-sizeof(uint64_t)];
    QNode() : status(READY_TO_USE), next(NULL) {}
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
    inline bool HasValidSuccessor(){
        return next > CANT_WAIT_FOR_NEXT;
    }
    
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct ABOLock{
#define MAX_RETRY (1L<<10)
    volatile uint64_t status __attribute__((aligned(CACHE_LINE_SIZE)));
    char buf[CACHE_LINE_SIZE-sizeof(uint64_t)];
    ABOLock(): status(UNLOCKED) {}
    inline bool Acquire(int64_t T) {
        uint64_t retryThreshold = 2;
        while(1){
            if(BOOL_CAS(&status, UNLOCKED, LOCKED) == true)
                return true;
            // back off
            volatile uint64_t retryCnt = 0;
            while(retryCnt ++ < retryThreshold) {
                if(GetFastClockTick() >= T)
                    return false; // abort
            }
            retryThreshold = (retryThreshold < MAX_RETRY ? retryThreshold << 1 : 2);
        }
    }
    
    inline void Release(int64_t T){
        status = UNLOCKED;
    }
    
};

ABOLock abLock;

struct HNode{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct ABOLock * parent __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode *  volatile lock __attribute__((aligned(CACHE_LINE_SIZE)));
    
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


int threshold;
int * thresholdAtLevel;

inline int GetThresholdAtLevel(int level){
    return thresholdAtLevel[level];
}

static inline void HandleHorizontalAbortion(HNode * L, QNode *I, int64_t patience);


static inline void CleanupReverseChain(QNode * node){
    while (node) {
        QNode * prev = node->next; /* here next is actually the prev */
        //I->status = READY_TO_USE;
        // All writes issued before must commit before declaring that the node is ready for reuse.
        // We need this because, we don't want the update to the "next" field reach after the owner of the node sees READY_TO_USE status
        COMMIT_ALL_WRITES();
        AtomicWrite(&(node->status),READY_TO_USE);
        node = prev;
    }
}

static inline void DealWithRestOfHorizontal(HNode * & L, QNode * &I, QNode * & prev, int64_t patience){
    while (1) {
        if(!BOOL_CAS(&(L->lock), I, NULL)) {
            // No unbounded wait...
            // while (I->next == NULL) ; // spin

#if 0 // Not beeded for A_BO_MCS
            // if it is a node owned by me (frontier) and we couldn't wait for the successor, we need to set our status to "ACQUIRE_PARENT" so that next time when we come here
            // we wait till the status is READY_TO_USE
            // If CAS failes, we will set it to READY_TO_USE ourselves.
            if(AtomicLoad(&(I->status)) == COHORT_START)
                AtomicWrite(&(I->status), ACQUIRE_PARENT);
#endif
            // Wait until out of patience or successor has enqueued.
            for( ;GetFastClockTick() < patience; ){
                if (AtomicLoad(&(I->next)) != NULL)
                    goto SUCC_ENQED;
            }
            
            if (!BOOL_CAS(&(I->next), NULL, CANT_WAIT_FOR_NEXT)) {
                uint64_t prevStatus;
SUCC_ENQED:     prevStatus = SWAP(&(I->next->status), ACQUIRE_PARENT);
                if(prevStatus == ABORTED) {
                    QNode * succ = I->next;
                    I->next = prev;
                    prev = I;
                    I = succ;
                } else {
                    // So far, I believe we don't need a COMMIT_ALL_WRITES(); here.
                    // This is because, we would not have updated the "next" field of this "I" node.
                    // Hence, there is no reordering between status and next fields.
                    // If the owner of the node sees READY_TO_USE, there will be no delayed update to the "next" field reaching it.
                    // However, there is one worry, can the update to the "status" which was "either ACQUIRE_PARENT or a legal passing value
                    // get reordered with READY_TO_USE?
                    AtomicWrite(&(I->status),READY_TO_USE);
                    return;
                }
            } else {
                return;
                /*
                 // Don't do AtomicWrite(&(I->status),READY_TO_USE); Successor is responsible for doing it
                 */
            }
        } else {
            // So far, I believe we don't need a COMMIT_ALL_WRITES(); here.
            // This is because, we would not have updated the "next" field of this "I" node.
            // Hence, there is no reordering between status and next fields.
            // If the owner of the node sees READY_TO_USE, there will be no delayed update to the "next" field reaching it.
            // However, there is one worry, can the update to the "status" which was "either ACQUIRE_PARENT or a legal passing value
            // get reordered with READY_TO_USE?
            AtomicWrite(&(I->status),READY_TO_USE);
            return;
        }
    }
    assert(0 && "Should never reach here");
}


static inline void HandleHorizontalAbortion(HNode * L, QNode *I, int64_t patience){
    QNode * prev = NULL;
    while(1) {
        if (I->HasValidSuccessor()) {
            uint64_t prevStatus = SWAP(&(I->next->status), ACQUIRE_PARENT);
            if(prevStatus == ABORTED){
                QNode * succ = I->next;
                I->next = prev;
                prev = I;
                I = succ;
            } else {
                // So far, I believe we don't need a COMMIT_ALL_WRITES(); here.
                // This is because, we would not have updated the "next" field of this "I" node.
                // Hence, there is no reordering between status and next fields.
                // If the owner of the node sees READY_TO_USE, there will be no delayed update to the "next" field reaching it.
                // However, there is one worry, can the update to the "status" which was ACQUIRE_PARENT in the SWAP operation
                // get reordered with READY_TO_USE? I hope not!
                AtomicWrite(&(I->status),READY_TO_USE);
                break;
            }
        } else {
            DealWithRestOfHorizontal(L, I, prev, patience);
            break;
        }
    }
    CleanupReverseChain(prev);
}


template<int level>
struct HMCS {
    static inline bool AcquireHelper(HNode * L, QNode *I, int64_t patience) {
        // Prepare the node for use.
        uint64_t prevStatus = SWAP(&(I->status), WAIT);
        QNode * pred;
        switch(prevStatus){
            case ABORTED: goto START_SPIN;
            case READY_TO_USE: break;
            //case WAIT: assert(0); /* depricated */ break;
            default:
                // Covers case COHORT_START, ACQUIRE_PARENT: assert(0 && "CASE ACQUIRE_PARENT");
                //while(I->status != READY_TO_USE); No unbounded wait
                for(; GetFastClockTick() < patience;) {
                    if(AtomicLoad(&(I->status)) == READY_TO_USE){
                        goto USE_QNODE;
                    }
                }
                // Abort
                // CAS with ACQUIRE_PARENT, so that next time when we want to use the node, we go through the default case
                if(CAS(&(I->status), WAIT, ACQUIRE_PARENT) !=  READY_TO_USE) {
                    // behavior is analogous to an ABORT, except that we don't set status = ABORTED
                    // The predecessor who has walked past me is reponsible for chaning the status to READY_TO_USE
                    return false;
                } // else I is READY_TO_USE fall through to USE_QNODE
        }
        
    USE_QNODE:
        I->next = NULL;
        // Updates must happen before swap
        COMMIT_ALL_WRITES();
        
        pred = (QNode *) SWAP(&(L->lock), I);
        if(!pred) {
            // I am the first one at this level
            // begining of cohort
            // Milind: I expect this write to not get reordered with a previous update to I->status since it is the same location
            I->status = COHORT_START;
            // Milind: I am not sure whether there is need to issue a lwsync fence here
            // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
            // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
            // the lock was passed to a descendent.
            // Does this mean, we should issue a fence just before starting the abort handling?
            
            // Acquire at next level if not at the top level
            if(L->parent->Acquire(patience))
                return true;
            HandleHorizontalAbortion(L, I, patience);
            return false;
        } else {
            // To avoid unbounded wait on I->next
            // pred->next = I;
            if(SWAP(&(pred->next), I) == CANT_WAIT_FOR_NEXT){
                // Free pred to be reused
                AtomicWrite(&(pred->status), READY_TO_USE);
                // Milind: Is this necessary to ensure that this write strictly preceeds the the next write I->status?
                // I am not sure.
                
                
                // This level is acquired, acquire parent ...
                // beginning of cohort
                // Milind: I expect this write to not get reordered with a previous update to I->status since it is the same location
                I->status = COHORT_START;
                // Milind: I am not sure whether there is need to issue a lwsync fence here
                // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
                // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
                // the lock was passed to a descendent.
                // Does this mean, we should issue a fence just before starting the abort handling?
                
                // Acquire at next level if not at the top level
                if(L->parent->Acquire(patience))
                    return true;
                HandleHorizontalAbortion(L, I, patience);
                return false;
            }
            
        START_SPIN:
            for(; GetFastClockTick() < patience;){
                uint64_t myStatus = AtomicLoad(&(I->status)); //I->status;
                if(myStatus < ACQUIRE_PARENT) {
                    return true;
                }
                if(myStatus == ACQUIRE_PARENT) {
                    // beginning of cohort
                    I->status = COHORT_START;
                    
                    // Milind: I am not sure whether there is need to issue a lwsync fence here
                    // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
                    // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
                    // the lock was passed to a descendent.
                    // Does this mean, we should issue a fence just before starting the abort handling?
                    
                    // This means this level is acquired and we can start the next level
                    if(L->parent->Acquire(patience))
                        return true;
                    HandleHorizontalAbortion(L, I, patience);
                    return false;
                }
                // spin back; (I->status == WAIT)
            }
            
            // Abort
            prevStatus = SWAP(&(I->status), ABORTED);
            if(prevStatus < ACQUIRE_PARENT){
                I->status = prevStatus;
                //Milind: I don't think we need lwsync here because we acquired the lock and there will be a lwsync at the end of the CS.
                return true; // got lock;
            }
            if(prevStatus == ACQUIRE_PARENT) {
                I->status = COHORT_START;
                // Milind: I am not sure whether there is need to issue a lwsync fence here
                // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
                // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
                // the lock was passed to a descendent.
                // Does this mean, we should issue a fence just before starting the abort handling?
                if(L->parent->Acquire(patience))
                    return true;
                HandleHorizontalAbortion(L, I, patience);
                return false;
            } else {
                return false;
            }
        }
    }
    
    static inline bool Acquire(HNode * L, QNode *I, int64_t patience){
        bool val = HMCS<level>::AcquireHelper(L, I, patience);
        FORCE_INS_ORDERING();
        return val;
    }
    
    static inline void HandleHorizontalPassing(HNode * L, QNode *I, uint64_t value, int64_t patience){
        QNode * prev = NULL;
        while(1) {
            if (I->HasValidSuccessor()) {
                uint64_t prevStatus = SWAP(&(I->next->status), value);
                if(prevStatus == ABORTED){
                    QNode * succ = I->next;
                    I->next = prev;
                    prev = I;
                    I = succ;
                } else {
                    // So far, I believe we don't need a COMMIT_ALL_WRITES(); here.
                    // This is because, we would not have updated the "next" field of this "I" node.
                    // Hence, there is no reordering between status and next fields.
                    // If the owner of the node sees READY_TO_USE, there will be no delayed update to the "next" field reaching it.
                    // However, there is one worry, can the update to the "status" which was ACQUIRE_PARENT in the SWAP operation
                    // get reordered with READY_TO_USE? I hope not!
                    AtomicWrite(&(I->status),READY_TO_USE);
                    break;
                }
            } else {
                L->parent->Release(patience);
                COMMIT_ALL_WRITES();
                // back from vertical passing
                DealWithRestOfHorizontal(L, I, prev, patience);
                break;
            }
        }
        CleanupReverseChain(prev);
    }
    
    inline static void ReleaseHelper(HNode * L, QNode *I, int64_t patience) {
        uint64_t curCount = I->status;
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
            L->parent->Release(patience);
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            QNode * prev = NULL;
            DealWithRestOfHorizontal(L, I, prev, patience);
            CleanupReverseChain(prev);
            return; // Released
        }
        HandleHorizontalPassing(L, I, curCount + 1, patience);
        return; // Released
    }
    
    inline static void Release(HNode * L, QNode *I, int64_t patience) {
        COMMIT_ALL_WRITES();
        HMCS<level>::ReleaseHelper(L, I, patience);
    }
};


typedef bool (*AcquireFP) (HNode *, QNode *, int64_t);
typedef void (*ReleaseFP) (HNode *, QNode *, int64_t);
struct A_BO_HMCS_T_LockWrapper{
    HNode * curNode;
    AcquireFP myAcquire;
    ReleaseFP myRelease;
    int curDepth;
    QNode I; // will be initialized to {READY_TO_USE, null}
    
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
    
    A_BO_HMCS_T_LockWrapper(HNode * h, int depth) : curNode(h), curDepth(depth) {
        switch(curDepth){
            case 1:  myAcquire = HMCS<1>::Acquire; myRelease = HMCS<1>::Release; break;
            case 2:  myAcquire = HMCS<2>::Acquire; myRelease = HMCS<2>::Release; break;
            case 3:  myAcquire = HMCS<3>::Acquire; myRelease = HMCS<3>::Release; break;
            case 4:  myAcquire = HMCS<4>::Acquire; myRelease = HMCS<4>::Release; break;
            case 5:  myAcquire = HMCS<5>::Acquire; myRelease = HMCS<5>::Release; break;
            default: assert(0 && "NYI");
        }
    }
    inline bool Acquire(int64_t patience = UINT64_MAX){
        return HMCS<2>::Acquire(curNode, &I, patience);
#if 0
        //myAcquire(curNode, I);
        switch(curDepth){
            case 1:  return HMCS<1>::Acquire(curNode, &I, patience);
            case 2:  return HMCS<2>::Acquire(curNode, &I, patience); 
            case 3:  return HMCS<3>::Acquire(curNode, &I, patience);
            case 4:  return HMCS<4>::Acquire(curNode, &I, patience); 
            case 5:  return HMCS<5>::Acquire(curNode, &I, patience);
            default: assert(0 && "NYI");
        }
#endif
        
    }
    
    inline void Release(uint64_t patience = UINT64_MAX){
        HMCS<2>::Release(curNode, &I, patience);
#if 0
        //myRelease(curNode, I);
        switch(curDepth){
            case 1:  HMCS<1>::Release(curNode, &I, patience); break;
            case 2:  HMCS<2>::Release(curNode, &I, patience); break;
            case 3:  HMCS<3>::Release(curNode, &I, patience); break;
            case 4:  HMCS<4>::Release(curNode, &I, patience); break;
            case 5:  HMCS<5>::Release(curNode, &I, patience); break;
            default: assert(0 && "NYI");
        }
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

A_BO_HMCS_T_LockWrapper * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1
    // only 2 levels supported.
    assert(levels == 2);
    
    int totalLocksNeeded = 0;
    for (int i=0; i < levels-1 /* only 2nd level locks allocated for BO lock at root */ ; i++) {
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
    for(int curLevel = 0 ; curLevel < levels - 1 /* only 2nd level locks allocated for BO lock at root */ ; curLevel++){
        if (tid%participantsAtLevel[curLevel] == 0) {
            // master, initialize the lock
            int lockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel];
            lastLockLocationEnd += maxThreads/participantsAtLevel[curLevel];
            HNode * curLock = new HNode();
            curLock->threshold = GetThresholdAtLevel(curLevel);
            curLock->parent = & abLock; /* The BO LOCK */
            //curLock->node = NULL;
            //curLock->node = new QNode();
            curLock->lock = NULL;
            lockLocations[lockLocation] = curLock;
        }
    }
#pragma omp barrier

#if 0 // Not needed for BO
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
#endif
    
#pragma omp barrier
    // return the lock to each thread
    return new A_BO_HMCS_T_LockWrapper(lockLocations[tid/participantsAtLevel[0]], levels);
}

#define UNDERLYING_LOCK A_BO_HMCS_T_LockWrapper

#ifdef SPLAY_TREE_DRIVER
#include "splay_driver.cpp"
#elif defined(CONTROLLED_NUMBER_OF_ABORTERS)
#include "splay_driver_few_aborters.cpp"
#elif defined(LOCAL_TREE_DRIVER)
#include "splay_driver_local_tree.cpp"
#elif defined(EMPTY_CS)
#include "empty_cs.cpp"
#else
#include "abort_driver.cpp"
#endif
