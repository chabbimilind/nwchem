//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define __STDC_LIMIT_MACROS
#include <stdint.h>
#include <omp.h>
#include <assert.h>
#include <sys/time.h>
#include <iostream>


#define CAS(a, b, c) __sync_val_compare_and_swap(a, b, c)
#define SWAP(a,b) __sync_lock_test_and_set(a, b)
#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

#define CACHE_LINE_SIZE (128)

enum ABORT_STATUS{LOCKED, UNLOCKED, ABORTED};

struct QNode{
    struct QNode * volatile next;
    volatile int status;
}__attribute__((aligned(CACHE_LINE_SIZE)));

QNode* volatile MCSLock = NULL;

    static bool Acquire(QNode* volatile* L, QNode* I, uint64_t waitCount) {
        I->next = NULL;
        I->status = LOCKED;
        QNode*   pred = (QNode*) __sync_lock_test_and_set((uint64_t*)L, I);

        if(pred) {
            pred->next = I;
            uint64_t curWaitCount = 0;
            while( (I->status == LOCKED) && (++curWaitCount < waitCount) ) ; // spin
            if(I->status == LOCKED) {
                if(__sync_bool_compare_and_swap(&(I->status), LOCKED, ABORTED)){
                    // aborted!!
                    return false;
                }
                // Predecessor exited, so we have the lock
            }
        }
        
        return true;
    }

    static void Release(QNode* volatile* L, QNode* I) {
        if(I->next) {
            if(!__sync_bool_compare_and_swap(&(I->next->status), LOCKED, UNLOCKED)) {
                // free all successors that are aborted
                Release(L, I->next);
            }
        } else {
            if(!__sync_bool_compare_and_swap((uint64_t*) L, I, NULL)) {
                // wait till some successor
                while(I->next == NULL) ; // spin

                if(!__sync_bool_compare_and_swap(&(I->next->status), LOCKED, UNLOCKED)) {
                    // free all successors that are aborted
                    Release(L, I->next);
                }
            }
        }
        delete I;
    }


volatile int var = 0;

struct InsideCS{
    volatile uint64_t f1 __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile uint64_t f2 __attribute__((aligned(CACHE_LINE_SIZE)));
}__attribute__((aligned(CACHE_LINE_SIZE)));


InsideCS gInsideCS;
void DoInsideCS(){
    gInsideCS.f1++;
    gInsideCS.f2++;
}

void DoOutsideCS(){
    // appx 4 Microsec
    volatile uint64_t i = 0;
    volatile uint64_t end = 4 * 1000;
    volatile uint64_t inc = 1;
    for (; i < end; i += inc)
        ;
}



int main(int argc, char *argv[]){
    
    int numThreads = atoi(argv[1]);
    int threshold = atoi(argv[2]);
    int levels = atoi(argv[3]);
    int * participantsAtLevel = (int * ) malloc(levels);
    for (int i = 0; i < levels; i++) {
        participantsAtLevel[i] = atoi(argv[4 + i]);
    }
    
    omp_set_num_threads(numThreads);
    
    int numIter = 144 * (0x4ffff) / numThreads;
    
    //int levels = 4;
    //int participantsAtLevel[] = {2, 4, 8, 16};
    //omp_set_num_threads(16);
    //int levels = 2;
    //int participantsAtLevel[] = {12, 36};
    //omp_set_num_threads(36);
    
    //int levels = 2;
    //int participantsAtLevel[] = {2, 4};
    //omp_set_num_threads(4);
    
    struct timeval start;
    struct timeval end;
    uint64_t elapsed;

//#define DOWORK

    
    
#pragma omp parallel
    {
        
        int tid = omp_get_thread_num();
        if(tid == 0)
            gettimeofday(&start, 0);
#ifdef USE_RAND
        struct drand48_data rBuf;
        srand48_r(tid, &rBuf);
        long int ticks;
#endif
        for(int i = 0; i < numIter; i++) {
            QNode * me = new QNode();
#ifdef USE_RAND
            lrand48_r(&rBuf, &ticks);
            uint64_t patience = 100000 + (abs(ticks) % 100000);
#else
//            uint64_t patience = UINT64_MAX;
            uint64_t patience = numIter % 10 == 0 ? 0 : UINT64_MAX;

#endif
            if (Acquire(&MCSLock, me,  patience)) {
            
#ifdef  DOWORK
                DoInsideCS();
#endif
              //  printf("Acquired %d!\n", tid);
            
//#define VALIDATE
#ifdef VALIDATE
                int lvar = var;
                var ++;
                assert(var == lvar + 1);
#endif
                Release(&MCSLock, me);
            } else {
               // printf("========Aborted %d!\n", tid);
            }
            
#ifdef  DOWORK
            DoOutsideCS();
#endif
            
        }
    }
    
    gettimeofday(&end, 0);
    elapsed = TIME_SPENT(start, end);
    double throughPut = (numIter * numThreads * 144 * 0x4ffffL) * 100000.0 / elapsed;
    std::cout<<"\n Throughput = " << throughPut;

    return 0;
}





