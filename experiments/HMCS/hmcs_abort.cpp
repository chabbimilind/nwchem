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
    QNode() : status(WAIT), next(NULL) {}
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
    HandleHorizontalAbortion(L, I, abortedNode);
}


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

static inline void DealWithRestOfHorizontal(HNode * & L, QNode * &I, QNode * & prev){
    while (1) {
        if(!BOOL_CAS(&(L->lock), I, NULL)) {
            // No unbounded wait...
            // while (I->next == NULL) ; // spin
            // if it is a node owned by me (frontier) and we couldn't wait for the successor, we need to set our status to "ACQUIRE_PARENT" so that next time when we come here
            // we wait till the status is READY_TO_USE
            // If CAS failes, we will set it to READY_TO_USE ourselves.
            if(AtomicLoad(&(I->status)) == COHORT_START)
                AtomicWrite(&(I->status), ACQUIRE_PARENT);
            
            if (!BOOL_CAS(&(I->next), NULL, CANT_WAIT_FOR_NEXT)) {
                uint64_t prevStatus = SWAP(&(I->next->status), ACQUIRE_PARENT);
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


static inline void HandleHorizontalAbortion(HNode * L, QNode *I, QNode * abortedNode){
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
            HandleVerticalAbortion(L->parent, &(L->node), abortedNode);
            // back from vertical abortion
            // We most certainly need  COMMIT_ALL_WRITES();  here.
            // HandleVerticalAbortion() would have written to the parent level shared node and possibly its uncles.
            // Those changes outght to be visible to a peer when it climbs to the parent level.
            COMMIT_ALL_WRITES();
            DealWithRestOfHorizontal(L, I, prev);
            break;
        }
    }
    CleanupReverseChain(prev);
}


template<int level>
struct HMCS {
    static inline QNode * Acquire(HNode * L, QNode *I, uint64_t patience = UINT64_MAX) {
        // Prepare the node for use.
        uint64_t prevStatus = SWAP(&(I->status), WAIT);
        QNode * pred;
        switch(prevStatus){
            case ABORTED: goto START_SPIN;
            case COHORT_START: goto GOT_LOCK;
            case READY_TO_USE: break;
            case WAIT: break;
            default:
                // Covers case ACQUIRE_PARENT: assert(0 && "CASE ACQUIRE_PARENT");
                //while(I->status != READY_TO_USE); No unbounded wait
                for(;patience > 0; patience--) {
                    if(AtomicLoad(&(I->status)) == READY_TO_USE){
                        goto USE_QNODE;
                    }
                }
                // Abort
                // CAS with ACQUIRE_PARENT, so that next time when we want to use the node, we go through the default case
                if(CAS(&(I->status), WAIT, ACQUIRE_PARENT) !=  READY_TO_USE) {
                    // behavior is analogous to an ABORT, except that we don't set status = ABORTED
                    // The predecessor who has walked past me is reponsible for chaning the status to READY_TO_USE
                    return I;
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
        GOT_LOCK:
            // Milind: I expect this write to not get reordered with a previous update to I->status since it is the same location
            I->status = COHORT_START;
            // Milind: I am not sure whether there is need to issue a lwsync fence here 
            // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
            // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
            // the lock was passed to a descendent.
            // Does this mean, we should issue a fence just before starting the abort handling?

            // Acquire at next level if not at the top level
            return HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
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

                // This means this level is acquired and we can start the next level
                return HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
            }
            
        START_SPIN:
            for(;patience > 0; patience--){
                uint64_t myStatus = AtomicLoad(&(I->status)); //I->status;
                if(myStatus < ACQUIRE_PARENT) {
                    return NULL;
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
                    return HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
                }
                // spin back; (I->status == WAIT)
            }
            
            // Abort
            prevStatus = SWAP(&(I->status), ABORTED);
            if(prevStatus < ACQUIRE_PARENT){
                I->status = prevStatus;
                //Milind: I don't think we need lwsync here because we acquired the lock and there will be a lwsync at the end of the CS.
                return NULL; // got lock;
            }
            if(prevStatus == ACQUIRE_PARENT) {
                I->status = COHORT_START;
                // Milind: I am not sure whether there is need to issue a lwsync fence here 
                // What if I abort at an ancestor, and pass the lock to one of my descendents? Will the descendents see this update to I->status?
                // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
                // the lock was passed to a descendent.
                // Does this mean, we should issue a fence just before starting the abort handling?
                return HMCS<level-1>::Acquire(L->parent, &(L->node), patience);
            } else {
                return I;
            }
        }
    }
    
    static inline bool AcquireWraper(HNode * L, QNode *I, uint64_t patience=UINT64_MAX){
        QNode * abortedNode = HMCS<level>::Acquire(L, I, patience);
        if (abortedNode) {
            // Milind: This is a very tricky place. All indications are that we need a lwsync (COMMIT_ALL_WRITES()) before starting to handle the abort.
            HandleVerticalAbortion(L, I, abortedNode);
            return false;
        }
        FORCE_INS_ORDERING();
        return true;
    }
    
    
    
    static inline void HandleHorizontalPassing(HNode * L, QNode *I, uint64_t value){
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
                HMCS<level - 1>::Release(L->parent, &(L->node));
                COMMIT_ALL_WRITES();
                // back from vertical passing
                DealWithRestOfHorizontal(L, I, prev);
                break;
            }
        }
        CleanupReverseChain(prev);
    }
    
    inline static bool Release(HNode * L, QNode *I) {
        uint64_t curCount = I->status;
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
            HMCS<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            QNode * prev = NULL;
            DealWithRestOfHorizontal(L, I, prev);
            CleanupReverseChain(prev);
            return true; // Released
        }
        HandleHorizontalPassing(L, I, curCount + 1);
        return true; // Released
    }
};


template <>
struct HMCS<1> {
    static inline QNode* Acquire(HNode * L, QNode *I, uint64_t patience= UINT64_MAX) {
        // Prepare the node for use.
        uint64_t prevStatus = SWAP(&(I->status), WAIT);
        QNode * pred;
        switch(prevStatus){
            case ABORTED: goto START_SPIN;
            case READY_TO_USE: break;
            case WAIT: break;
            case UNLOCKED:
                //while(I->status != READY_TO_USE); No unbounded wait
                uint64_t statusAtDefaultCase;
                for(;patience > 0; patience--) {
                    if(AtomicLoad(&(I->status)) == READY_TO_USE){
                        goto USE_QNODE;
                    }
                }
                // Abort
                // CAS  UNLOCKED, so that next time when we want to use the node, we go through the UNLOCKED case unless it is updated to READY_TO_USE
                if(CAS(&(I->status), WAIT, UNLOCKED) !=  READY_TO_USE) {
                    // behavior is analogous to an ABORT, except that we don't set status = ABORTED
                    // The predecessor who has walked past me is reponsible for chaning the status to READY_TO_USE
                    return I;
                } // else I is READY_TO_USE break to USE_QNODE
                break;
            default:assert(0 && "Should never reach here");
        }
        
    USE_QNODE:
        I->next = NULL;
        // Updates must happen before swap
        COMMIT_ALL_WRITES();
        
        pred = (QNode *) SWAP(&(L->lock), I);
        if(pred){
            // Avoid unbounded wait for I->next
            // pred->next = I;
            if(SWAP(&(pred->next), I) == CANT_WAIT_FOR_NEXT){
                // Free pred to be reused
                AtomicWrite(&(pred->status), READY_TO_USE);

                // Milind: Is this necessary to ensure that this write strictly precedes the the next write I->status?
                // I am not sure.


                // This level is acquired ...
                I->status = UNLOCKED;
                return NULL; // got lock;
            }
            
        START_SPIN:
            for(;patience > 0;patience--){
                uint64_t myStatus = I->status;
                if(myStatus == UNLOCKED) {
                    return NULL; // got lock;
                }
            }
            // Abort
            uint64_t prevStatus = SWAP(&(I->status), ABORTED);
            if(prevStatus == UNLOCKED) {
                I->status = UNLOCKED;
                return NULL; // got lock;
            }
            return I;
        } else {
            I->status = UNLOCKED;
            // Milind: I am not sure whether there is need to issue a lwsync fence here 
            // What if I abort here ancestor, and pass the lock to one of my descendants? Will the descendants see this update to I->status?
            // As a side note, this was not a problem in HMCS because there was a guarantee that an lwsync was issued as a part of the end of CS before
            // the lock was passed to a descendent.
            // Does this mean, we should issue a fence just before starting the abort?
            // More note: I don't think we need the same lwsync at the Acquire<1> level since no one else will share the I node.

        }
        return NULL;
    }
    
    static inline bool AcquireWraper(HNode * L, QNode *I, uint64_t patience=UINT64_MAX){
        QNode * abortedNode = Acquire(L, I, patience);
        if (abortedNode) {
            // Milind: This is a very tricky place. All indications are we need an lwsync() before beginning an abort. But this one does not really start a handling an abort.
            return false;
        }
        FORCE_INS_ORDERING();
        return true;
    }
    
    static inline void DealWithRestOfLevel1(HNode * & L, QNode * &I, QNode * & prev){
        while (1) {
            if(!BOOL_CAS(&(L->lock), I, NULL)) {
                // No unbounded wait...
                // while (I->next == NULL) ; // spin
                
                if (!BOOL_CAS(&(I->next), NULL, CANT_WAIT_FOR_NEXT)) {
                    uint64_t prevStatus = SWAP(&(I->next->status), UNLOCKED);
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
                        // However, there is one worry, can the update to the "status" which was UNLOCKED
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
                // However, there is one worry, can the update to the "status" which was UNLOCKED
                // get reordered with READY_TO_USE?
                AtomicWrite(&(I->status),READY_TO_USE);
                return;
            }
        }
        assert(0 && "Should never reach here");
    }
    
    static inline void HandleHorizontalPassing(HNode * L, QNode *I){
        QNode * prev = NULL;
        while(1) {
            if (I->HasValidSuccessor()) {
                uint64_t prevStatus = SWAP(&(I->next->status), UNLOCKED);
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
                    // However, there is one worry, can the update to the "status" which was UNLOCKED in the SWAP operation
                    // get reordered with READY_TO_USE? I hope not!
 
                    AtomicWrite(&(I->status),READY_TO_USE);
                    break;
                }
            } else {
                DealWithRestOfLevel1(L, I, prev);
                break;
            }
        }
        CleanupReverseChain(prev);
    }
    
    inline static bool Release(HNode * L, QNode *I) {
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
            curLock->node.status = WAIT;
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
    leafHNode->node.status = WAIT;
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


