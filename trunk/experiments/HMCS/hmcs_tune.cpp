//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//

#include "util.h"

struct QNode{
    struct QNode * volatile next __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile uint64_t status __attribute__((aligned(CACHE_LINE_SIZE)));
    QNode() : status(WAIT), next(NULL) {
        
    }
    
    inline void Reuse(){
        status = WAIT;
        next = NULL;
    }
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct HMCS{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct HMCS * parent __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode *  volatile lock __attribute__((aligned(CACHE_LINE_SIZE)));
    struct QNode  node __attribute__((aligned(CACHE_LINE_SIZE)));
    
    inline bool IsTopLevel() {
        return parent == NULL ? true : false;
    }
    
    inline uint64_t GetThreshold()const {
        return threshold;
    }

    inline uint64_t SetThreshold(uint64_t t) {
         threshold = t;
    }
    

}__attribute__((aligned(CACHE_LINE_SIZE)));


int threshold;
int * thresholdAtLevel;

inline int GetThresholdAtLevel(int level){
    // TODO: make it tunable
    //return threshold;
    return thresholdAtLevel[level];
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
inline void AcquireParent(HMCS * L, QNode *I) {
    //QNode * I2 = new QNode();
    //L->node = I2;
    //Acquire(L->parent, I2);
    
    // prepare L->node;
    L->node.Reuse();
    Acquire(L->parent, &(L->node));
}


void Acquire(HMCS * L, QNode *I) {
    QNode * pred = SWAP(&(L->lock), I);
    if(!pred) {
        // I am the first one at this level
        // Acquire at next level if not at the top level
        if(!(L->IsTopLevel())) {
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

bool Release(HMCS * L, QNode *I, bool tryRelease=false);
inline void NormalMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    if(I->next) {
        I->next->status = val;
    } else {
        QNode * casVal = CAS(&(L->lock), I, NULL);
        if (casVal != I){
            while(I->next == NULL);
            I->next->status = val;
        }
    }
}

inline bool TryMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    if(I->next) {
        I->next->status = val;
        return true;
    } else {
        // found no successor so, did not release
        return false;
    }
}


bool Release(HMCS * L, QNode *I, bool tryRelease) {
    uint64_t curCount = I->status;
    
    // Top level release is usual MCS
    if(L->IsTopLevel()) {
        if(tryRelease) {
            return TryMCSReleaseWithValue(L, I, curCount);
        }
        NormalMCSReleaseWithValue(L, I, curCount);
        return true;
    }
    
    // Lower level releases
    
    if(curCount == L->GetThreshold()) {
        
        // if I have successors, we'll try release
        if( tryRelease || I->next) {
            bool releaseVal = Release(L->parent, &(L->node), true /* try release */);
            if(releaseVal){
                // Tap successor at this level and ask to spin acquire next level lock
                NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
                return true; // released
            }
            
            // retaining lock
            // if tryRelease == true, pass it to descendents
            if (tryRelease) {
                return false; // not released
            }
            // pass it to peers
            // Tap successor at this level
            I->next->status=  COHORT_START; /* give one full chunk */
            return true; //released
            
        }
        
        // NO KNOWN SUCCESSORS / DESCENDENTS
        // reached threshold and have next level
        // release to next level
        
        Release(L->parent, &(L->node));
        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        return true; // Released
    }
    
    // Not reached threshold
    if(I->next) {
        I->next->status = curCount + 1;
        return true; // Released
    } else {
                // NO KNOWN SUCCESSOR, so release
        Release(L->parent, &(L->node));

        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        return true; // Released
    }
}


int main(int argc, char *argv[]){
    
    int totalIters = atoi(argv[1]);
    int numThreads = atoi(argv[2]);
    int levels = atoi(argv[3]);
    int * participantsAtLevel = (int * ) malloc(levels);
    thresholdAtLevel = (int * ) malloc(levels);
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[4 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[4 + 2*i + 1]);
    }
    
    omp_set_num_threads(numThreads);
    
    int numIter = totalIters / numThreads;

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
    
    
#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        HMCS * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        
        if(tid == 0)
            gettimeofday(&start, 0);
        
        QNode me;
        for(int i = 0; i < numIter; i++) {
            me.Reuse();
            Acquire(hmcs, &me);
            
#ifdef  DOWORK
            DoWorkInsideCS();
#endif

#ifdef VALIDATE
            int lvar = var;
            var ++;
            assert(var == lvar + 1);
#endif
            Release(hmcs, &me);
            
#ifdef  DOWORK
            DoWorkOutsideCS();
#endif
            
        }
    }
    gettimeofday(&end, 0);
    elapsed = TIME_SPENT(start, end);
    double throughPut = (numIter * numThreads) * 1000000.0 / elapsed;
    std::cout<<"\n Throughput = " << throughPut;
    return 0;
}





