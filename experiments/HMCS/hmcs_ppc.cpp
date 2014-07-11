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
        COMMIT_ALL_WRITES();
    }
}__attribute__((aligned(CACHE_LINE_SIZE)));

struct HMCS{
    int threshold __attribute__((aligned(CACHE_LINE_SIZE)));
    struct HMCS * parent __attribute__((aligned(CACHE_LINE_SIZE)));
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

HMCS ** lockLocations __attribute__((aligned(CACHE_LINE_SIZE)));

HMCS * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1
    
    int totalLocksNeeded = 0;
    for (int i=0; i < levels; i++) {
        totalLocksNeeded += maxThreads / participantsAtLevel[i] ;
    }
#pragma omp single
    {
        //lockLocations = new HMCS*[totalLocksNeeded];
        // use memalign for alignemnt new does not ensure alignment
        lockLocations = (HMCS**)memalign(CACHE_LINE_SIZE, sizeof(HMCS*) * totalLocksNeeded);
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

static void Acquire(HMCS * L, QNode *I);
static inline void AcquireParent(HMCS * L, QNode *I) {
    //QNode * I2 = new QNode();
    //L->node = I2;
    //Acquire(L->parent, I2);
    
    // prepare L->node;
    L->node.Reuse();
    Acquire(L->parent, &(L->node));
}



/*
 An isync instruction causes the processor to complete execution of all previous instructions and then to discard instructions (which may have begun execution) following the isync. After the isync is executed, the following instructions then begin execution. isync is used in locking code to ensure that the loads following entry into the critical section are not performed (because of aggressive out-of-order or speculative execution in the processor) until the lock is granted.
 */

// NOTE: Replace Acquire with Acquire(); ISYNC();

static inline void Acquire(HMCS * L, QNode *I) {
    QNode * pred = (QNode *) SWAP(&(L->lock), I);
    
    if(!pred) {
        // I am the first one at this level
        // begining of cohort
        I->status = COHORT_START;

        FORCE_INS_ORDERING();

        // Acquire at next level if not at the top level
        if(!(L->IsTopLevel())) {
            // This means this level is acquired and we can start the next level
            AcquireParent(L, I);
        }
    } else {
        pred->next = I;
        
        // ISYNC ... we dont want to start spinning before setting pred->next
        FORCE_INS_ORDERING();
        // Contemplating if this needs to be an LWSYNC or ISYNC
        //COMMIT_ALL_WRITES();

        
        // JohnMC optimize 2 tests and reduce load when WAIT has ended.
        for(;;){
            uint64_t myStatus = I->status;
            if(myStatus < ACQUIRE_PARENT) {
                FORCE_INS_ORDERING();
                break;
            }
            if(myStatus == ACQUIRE_PARENT) {
                // beginning of cohort
                I->status = COHORT_START;
                
                FORCE_INS_ORDERING();

                // This means this level is acquired and we can start the next level
                AcquireParent(L, I);
                break;
            }
            // spin back; (I->status == WAIT)
        }
    }
}

static inline void AcquireWraper(HMCS * L, QNode *I) {
    Acquire(L, I);
    FORCE_INS_ORDERING();
}

static bool Release(HMCS * L, QNode *I, bool tryRelease=false);
inline static void NormalMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
    } else {
        if (BOOL_CAS(&(L->lock), I, NULL))
            return;
        while( (succ=I->next) == NULL);
        succ->status = val;
    }
}

inline static  bool TryMCSReleaseWithValue(HMCS * L, QNode *I, uint64_t val){
    QNode * succ = I->next;
    if(succ) {
        succ->status = val;
        return true;
    } else {
        // found no successor so, did not release
        return false;
    }
}


inline static bool Release(HMCS * L, QNode *I, bool tryRelease) {
    
    uint64_t curCount = I->status;
    
    QNode * succ;
    
    // Top level release is usual MCS
    if(L->IsTopLevel()) {
        if(tryRelease) {
            bool retVal = TryMCSReleaseWithValue(L, I, curCount);
            COMMIT_ALL_WRITES();
            return retVal;

        }
        NormalMCSReleaseWithValue(L, I, curCount);
        COMMIT_ALL_WRITES();
        return true;
    }
    
    // Lower level releases
    
    if(curCount == L->GetThreshold()) {
        
        succ  = I->next;
        // if I have successors, we'll try release
        if( tryRelease || succ) {
            bool releaseVal = Release(L->parent, &(L->node), true /* try release */);
            if(releaseVal){
                // Tap successor at this level and ask to spin acquire next level lock
                NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
                COMMIT_ALL_WRITES();
                return true; // released
            }
            
            // retaining lock
            // if tryRelease == true, pass it to descendents
            if (tryRelease) {
                COMMIT_ALL_WRITES();
                return false; // not released
            }
            // pass it to peers
            // Tap successor at this level
            succ->status=  COHORT_START; /* give one full chunk */
            COMMIT_ALL_WRITES();
            return true; //released
            
        }
        
        // NO KNOWN SUCCESSORS / DESCENDENTS
        // reached threshold and have next level
        // release to next level
        
        Release(L->parent, &(L->node));
        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        COMMIT_ALL_WRITES();
        return true; // Released
    }
    
    succ = I->next;
    // Not reached threshold
    if(succ) {
        succ->status = curCount + 1;
        COMMIT_ALL_WRITES();
        return true; // Released
    } else {
                // NO KNOWN SUCCESSOR, so release
        Release(L->parent, &(L->node));

        // Tap successor at this level and ask to spin acquire next level lock
        NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
        COMMIT_ALL_WRITES();
        return true; // Released
    }
}

inline static bool ReleaseWrapper(HMCS * L, QNode *I) {
    COMMIT_ALL_WRITES();
    Release(L, I);
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
        
#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif

        
        HMCS * hmcs = LockInit(tid, size, levels, participantsAtLevel);

        if(tid == 0)
            gettimeofday(&start, 0);
        
        QNode me;
        for(int i = 0; i < numIter; i++) {
            me.Reuse();
            AcquireWraper(hmcs, &me);
            
#ifdef  DOWORK
            DoWorkInsideCS();
#endif

#ifdef VALIDATE
            int lvar = var;
            var ++;
            assert(var == lvar + 1);
#endif
            ReleaseWrapper(hmcs, &me);
            
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





