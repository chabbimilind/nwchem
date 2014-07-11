//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//
#include "util.h"

struct ClassicalMCSNode{
    struct ClassicalMCSNode * volatile next __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile bool status __attribute__((aligned(CACHE_LINE_SIZE)));
}__attribute__((aligned(CACHE_LINE_SIZE)));

ClassicalMCSNode* volatile MCSLock __attribute__((aligned(CACHE_LINE_SIZE)));


static inline void AcquireClassicalMCS(ClassicalMCSNode* volatile* L, ClassicalMCSNode* I) {
    I->next = NULL;
    I->status = LOCKED;
    ClassicalMCSNode*   pred = (ClassicalMCSNode*) SWAP((void**)L, I);
    
    if(pred) {
        pred->next = I;
        while(I->status == LOCKED) ; // spin
    }
}

static inline void ReleaseClassicalMCS(ClassicalMCSNode* volatile* L, ClassicalMCSNode* I) {
    if(I->next == NULL) {
        if(BOOL_CAS((void**) L, I, NULL))
            return; // No successor, hence return
        
        // Some successor got in, wait till he sets my next field
        // wait till some successor
        while(I->next == NULL) ; // spin
    }
    
    // Tap the successor
    I->next->status = UNLOCKED;
}


int main(int argc, char *argv[]){
    if(argc != 3) {
        printf("Usage:%s <num_iters> <num_threads>", argv[0]);
        return -1;
    }
    int numThreads = atoi(argv[2]);
    int numIter = atoi(argv[1]) / numThreads;
    omp_set_num_threads(numThreads);
    
    struct timeval start;
    struct timeval end;
    uint64_t elapsed;
    
    
#pragma omp parallel
    {
        
        ClassicalMCSNode me;
        int tid = omp_get_thread_num();
        
        // Start timer
        if(tid == 0)
            gettimeofday(&start, 0);
        
        for(int i = 0; i < numIter; i++) {
            AcquireClassicalMCS(&MCSLock, &me);
            
#ifdef  DOWORK
            DoWorkInsideCS();
#endif

#ifdef VALIDATE
            int lvar = var;
            var ++;
            assert(var == lvar + 1);
#endif
            ReleaseClassicalMCS(&MCSLock, &me);
            
            
#ifdef  DOWORK
            DoWorkOutsideCS();
#endif
            
        }
        
    }
    
    // End timer
    gettimeofday(&end, 0);
    elapsed = TIME_SPENT(start, end);
    // Compute Throughput = locks per second
    double throughPut = (numIter * numThreads) * 1000000.0 / elapsed;
    std::cout<<"\n Throughput = " << throughPut;
    
    return 0;
}





