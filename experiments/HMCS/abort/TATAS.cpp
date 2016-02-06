#include "util.h" 
  
int * thresholdAtLevel;
 
struct TATASLock{
    volatile uint64_t L __attribute__((aligned(CACHE_LINE_SIZE)));
    TATASLock(): L(UNLOCKED){}
    inline bool Acquire(int64_t patience){
        while(1) {
                while(L == LOCKED) {
			if (GetFastClockTick() >= patience)
				return false;
                }
                if(BOOL_CAS(&L, UNLOCKED, LOCKED) == true)
                        break;
        }
        FORCE_INS_ORDERING();
	return true;
    }

    inline void Release(int64_t patience){
        COMMIT_ALL_WRITES();
        L = UNLOCKED;
    }
};

TATASLock * tataslock;
TATASLock * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
#pragma omp barrier
#pragma omp single
    {
        tataslock = new TATASLock();
    }
#pragma omp barrier
    return tataslock;
}

#define UNDERLYING_LOCK TATASLock

#ifdef SPLAY_TREE_DRIVER
#include "splay_driver.cpp"
#elif defined(CONTROLLED_NUMBER_OF_ABORTERS)
#include "splay_driver_few_aborters.cpp"
#else
#include "abort_driver.cpp"
#endif
