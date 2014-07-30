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
        // Updates must happen before swap
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
    return thresholdAtLevel[level];
}


typedef bool (*ReleaseFP)(HMCS * L, QNode *I);
static ReleaseFP ReleaseLockReal __attribute__((aligned(CACHE_LINE_SIZE)));

static void Acquire(HMCS * L, QNode *I);
static inline void AcquireParent(HMCS * L) {
    Acquire(L->parent, &(L->node));
}

#define ACQUIRE_NEXT_LEVEL_MCS_LOCK(L) do{I=&(L->node); L=L->parent; goto START;} while(0)

static inline void Acquire(HMCS * L, QNode *I) {
START:
    // Prepare the node for use.
    I->Reuse();
    QNode * pred = (QNode *) SWAP(&(L->lock), I);
    if(!pred) {
        // I am the first one at this level
        // begining of cohort
        I->status = COHORT_START;
        // Acquire at next level if not at the top level
        if(!(L->IsTopLevel())) {
            // This means this level is acquired and we can start the next level
            ACQUIRE_NEXT_LEVEL_MCS_LOCK(L);
        }
    } else {
        pred->next = I;
        for(;;){
            uint64_t myStatus = I->status;
            if(myStatus < ACQUIRE_PARENT) {
                break;
            }
            if(myStatus == ACQUIRE_PARENT) {
                // beginning of cohort
                I->status = COHORT_START;
                // This means this level is acquired and we can start the next level
                ACQUIRE_NEXT_LEVEL_MCS_LOCK(L);
                break;
            }
            // spin back; (I->status == WAIT)
        }
    }
}

#define AcquireWraper(L, I) do {\
    Acquire(L, I);\
    FORCE_INS_ORDERING(); }while(0)

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




template<int level>
struct LockRelease {
    inline static bool Release(HMCS * L, QNode *I
#ifdef TRY_RELEASE
, bool tryRelease=false
#endif
) {

        uint64_t curCount = I->status;
        QNode * succ;
        
        // Lower level releases
        if(curCount == L->GetThreshold()) {
#ifdef TRY_RELEASE
            succ  = I->next;
            // if I have successors, we'll try release
            if( tryRelease || succ) {
                bool releaseVal = LockRelease<level - 1>::Release(L->parent, &(L->node), true /* try release */);
                if(releaseVal){
                    COMMIT_ALL_WRITES();
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
                succ->status=  COHORT_START; /* give one full chunk */
                return true; //released
            }
#endif            
            // NO KNOWN SUCCESSORS / DESCENDENTS
            // reached threshold and have next level
            // release to next level
            LockRelease<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
            return true; // Released
        }
        
        succ = I->next;
        // Not reached threshold
        if(succ) {
            succ->status = curCount + 1;
            return true; // Released
        } else {
            // No known successor, so release
            LockRelease<level - 1>::Release(L->parent, &(L->node));
            COMMIT_ALL_WRITES();
            // Tap successor at this level and ask to spin acquire next level lock
            NormalMCSReleaseWithValue(L, I, ACQUIRE_PARENT);
            return true; // Released
        }
    }
    
};

template <>
struct LockRelease<1> {
    inline static bool Release(HMCS * L, QNode *I
#ifdef TRY_RELEASE
, bool tryRelease=false
#endif
) {
        // Top level release is usual MCS
        // At the top level MCS we always writr COHORT_START since
        // 1. It will release the lock
        // 2. Will never grow large
        // 3. Avoids a read from I->status
#ifdef TRY_RELEASE
        if(tryRelease) {
            bool retVal = TryMCSReleaseWithValue(L, I, COHORT_START);
            return retVal;
        }
#endif
        NormalMCSReleaseWithValue(L, I, COHORT_START);
        return true;
    }
};

#define ReleaseWrapper(L, I, level) do{\
    COMMIT_ALL_WRITES();\
    LockRelease<level>::Release(L, I); }while(0)

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
    
    
#pragma omp single
    {
        switch (levels) {
            case 1:
                ReleaseLockReal = LockRelease<1>::Release;
                break;
            case 2:
                ReleaseLockReal = LockRelease<2>::Release;
                break;
            case 3:
                ReleaseLockReal = LockRelease<3>::Release;
                break;
            case 4:
                ReleaseLockReal = LockRelease<4>::Release;
                break;
            case 5:
                ReleaseLockReal = LockRelease<5>::Release;
                break;
            case 6:
                ReleaseLockReal = LockRelease<6>::Release;
                break;
            case 7:
                ReleaseLockReal = LockRelease<7>::Release;
                break;
            case 8:
                ReleaseLockReal = LockRelease<8>::Release;
                break;
            default:
                assert(0 && "Release > 8 NYI");
                break;
        }
    }
    
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
static inline void OutsideCriticalSection(){
#ifdef  DOWORK
    DoWorkOutsideCS();
#endif
}

int main(int argc, char *argv[]){
    
    uint64_t totalIters = atol(argv[1]);
    int numThreads = atoi(argv[2]);
    int levels = atoi(argv[3]);
    int * participantsAtLevel = (int * ) malloc(levels);
    thresholdAtLevel = (int * ) malloc(levels);
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[4 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[4 + 2*i + 1]);
    }
    
    omp_set_num_threads(numThreads);
    uint64_t numIter = totalIters / numThreads;
    struct timeval start;
    struct timeval end;
    uint64_t elapsed;
    
    // Set up alarm after 3 minutes to time out
    signal(SIGALRM, AlarmHandler);
    alarm(ALARM_TIME);
    
    
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
        
        switch (levels) {
            case 1:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 1);
                    OutsideCriticalSection();
                }
                break;
            case 2:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 2);
                    OutsideCriticalSection();
                }
                break;
            case 3:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 3);
                    OutsideCriticalSection();
                }
                break;
            case 4:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 4);
                    OutsideCriticalSection();
                }
                break;
            case 5:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 5);
                    OutsideCriticalSection();
                }
                break;
            case 6:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 6);
                    OutsideCriticalSection();
                }
                break;
            case 7:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 7);
                    OutsideCriticalSection();
                }
                break;
            case 8:
                for(uint64_t i = 0; i < numIter; i++) {
                    AcquireWraper(hmcs, &me);
                    CriticalSection();
                    ReleaseWrapper(hmcs, &me, 8);
                    OutsideCriticalSection();
                }
                break;
            default:
                assert(0 && "ReleaseWrapper > 8 NYI" );
                break;
        }
        
    }
    gettimeofday(&end, 0);
    elapsed = TIME_SPENT(start, end);
    double throughPut = (numIter * numThreads) * 1000000.0 / elapsed;
    std::cout<<"\n Throughput = " << throughPut << "\n";
    return 0;
}

