//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include <stdio.h>
#include <stdint.h>
#include <omp.h>
#include <assert.h>

#define WAIT (0xffffffffffffffff)
#define ACQUIRE_PARENT (0xfffffffffffffffe)
#define COHORT_START (0x1)

#define CAS(a, b, c) __sync_val_compare_and_swap(a, b, c)
#define SWAP(a,b) __sync_lock_test_and_set(a, b)

#define CACHE_LINE_SIZE (128)

struct QNode{
    struct QNode * next;
    volatile uint64_t status;
    QNode() : status(WAIT), next(NULL) {
        
    }
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct HMCS{
    int threshold;
    struct HMCS * parent;
    struct QNode *  lock;
    struct QNode  node;
}__attribute__((aligned(CACHE_LINE_SIZE)));



int GetThresholdAtLevel(int leve){
    // TODO: make it tunable
    return 64;
}

/*
 
 8 cores per CPU
 4 CPUs per node
 2 nodes
 ==>
 levels = 3
 participantsAtLevel = {8, 32, 64};
 
 */

HMCS ** lockLocations;

HMCS * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1
    
    int totalLocksNeeded = 0;
    for (int i=0; i < levels; i++) {
        totalLocksNeeded += maxThreads / participantsAtLevel[i] ;
    }
#pragma omp single
    {
        lockLocations = new HMCS*[totalLocksNeeded];
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

void Acquire(HMCS * L, QNode *I);
void AcquireParent(HMCS * L, QNode *I) {
    //QNode * I2 = new QNode();
    //L->node = I2;
    //Acquire(L->parent, I2);
    
    // prepare L->node;
    L->node.status = WAIT;
    L->node.next = NULL;
    
    Acquire(L->parent, &(L->node));
}


void Acquire(HMCS * L, QNode *I) {
    QNode * pred = SWAP(&(L->lock), I);
    if(!pred) {
        // I am the first one at this level
        // Acquire at next level if not at the top level
        if(L->parent) {
            AcquireParent(L, I);
        }
        // begining of cohort
        I->status = COHORT_START;
    } else {
        pred->next = I;
        
        // Wait for tap from predecessor
        while(I->status == WAIT) ;
        
        if(I->status == ACQUIRE_PARENT) {
            AcquireParent(L, I);
            // beginning of cohort
            I->status = COHORT_START;
        }
    }
}

void Release(HMCS * L, QNode *I);

void Release(HMCS * L, QNode *I) {
    uint64_t curCount = I->status;
    assert(curCount != WAIT);
    assert(curCount != ACQUIRE_PARENT);
    
    if(curCount == L->threshold && L->parent) {
        
        /*
         //TODO
         if(I->next) {
         TryRelease(L->parent, L->node);
         }*/
        
        // reached threshold and have next level
        // release to next level
        Release(L->parent, &(L->node));
        // we can free L->node now
        //delete L->node;
        //L->node = NULL;
        
        // Tap successor at this level and ask to spin acquire next level lock
        if(I->next) {
            I->next->status = ACQUIRE_PARENT;
        } else {
            // No know successor
            QNode * casVal = CAS(& (L->lock), I, NULL);
            if (casVal != I){
                while(I->next == NULL);
                I->next->status = ACQUIRE_PARENT;
            }
        }
    } else {
        // either top level or not reached threshold
        if(I->next) {
            I->next->status = curCount + 1;
        } else {
            uint64_t tapVal = L->parent ? ACQUIRE_PARENT : curCount + 1;
            if(L->parent){
                // release to parent
                if(I == L->lock) {
                    Release(L->parent, &(L->node));
                }
            }
            
            QNode * casVal = CAS(&(L->lock), I, NULL);
            if (casVal != I){
                while(I->next == NULL);
                I->next->status = tapVal;
            }
        }
    }
}


volatile int var = 0;

main(){
    //    int levels = 4;
    //    int participantsAtLevel[] = {2, 4, 8, 16};
    //    omp_set_num_threads(16);
    
    int levels = 2;
    int participantsAtLevel[] = {2, 4};
    omp_set_num_threads(4);
    
#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        HMCS * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        
        for(int i = 0; i < 0xffffff; i++) {
            QNode me;
            Acquire(hmcs, &me);
            printf("Acquired %d!\n", tid);
            
            int lvar = var;
            var ++;
            assert(var == lvar + 1);
            Release(hmcs, &me);
            
        }
        
#pragma omp barrier
        
    }
}



