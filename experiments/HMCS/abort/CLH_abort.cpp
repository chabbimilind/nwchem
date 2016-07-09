#include "util.h" 
  
int * thresholdAtLevel;

typedef enum {waiting,      // lock is held
                available,    // lock is free
                leaving,      // node owner is giving up
                transient,    // successor is giving up
                recycled}     // no pointers to node remain
      clh_status;

  struct clh_qnode {
      volatile clh_status status __attribute__((aligned(CACHE_LINE_SIZE)));
      volatile struct clh_qnode *volatile prev __attribute__((aligned(CACHE_LINE_SIZE)));
      char buf[CACHE_LINE_SIZE-sizeof(struct clh_qnode *)];

  } __attribute__((aligned(CACHE_LINE_SIZE)));;
  
  typedef volatile clh_qnode *clh_qnode_ptr;
  typedef clh_qnode_ptr clh_try_lock;

__thread clh_qnode_ptr  I;

struct CLHAbortableLock{
	volatile clh_try_lock L __attribute__((aligned(CACHE_LINE_SIZE)));
	CLHAbortableLock(): L(0){
		L = new clh_qnode();
		L->prev = 0;
		L->status=available;
	}
	inline bool Acquire(int64_t T){
		clh_status stat;

		I->status = waiting;
		clh_qnode_ptr pred = SWAP(&L, I);

		// check lock once before querying timer -- optimization
		if (pred->status == available) {
			I->prev = pred;
			return true;
		}

		while (GetFastClockTick() < T) {
			stat = pred->status;
			if (stat == available) {
				I->prev = pred;
				return true;
			}
			if (stat == leaving) {
				clh_qnode_ptr temp = pred->prev;
				pred->status = recycled;
				pred = temp;
			}
			// stat might also be transient,
			// if somebody left the queue just before I entered
		}

		// timed out

		while (1) {
			while (pred->status == transient);  // spin
			stat = SWAP(&pred->status, transient);
			if (stat == available) {
				I->prev = pred;
				return true;
			}

			if (stat == leaving) {
				clh_qnode_ptr temp = pred->prev;
				pred->status = recycled;
				pred = temp;
				continue;
			}
			break;          // stat == waiting
		}
		I->prev = pred;     // so successor can find it

		// indicate leaving, so successor can't leave
		while (1) {
			stat = CAS(&I->status, waiting, leaving);
			if (stat == waiting) break;
			while (I->status != waiting);       // spin
		}

		// if last process in line, link self out
		if (BOOL_CAS(&L, I, pred)) {
			pred->status = waiting;
			return false;
		}

		// not last in line
		while (1) {
			stat = I->status;
			if (stat == recycled) {
				pred->status = waiting;
				return false;
			}
		}

		FORCE_INS_ORDERING();
		return true;
	}

	inline void Release(int64_t patience){
		COMMIT_ALL_WRITES();
		clh_qnode_ptr * addrI = & I;
		clh_qnode_ptr pred = (*addrI)->prev;
		while (!BOOL_CAS(&(*addrI)->status, waiting, available)) {
			// can't set my node to available if it's currently transient
			while ((*addrI)->status == transient);  // spin
		}
		I = pred;
	}
};

CLHAbortableLock * clhAbortablelock;
CLHAbortableLock * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
	I = new clh_qnode();
#pragma omp barrier
#pragma omp single
	{
		clhAbortablelock = new CLHAbortableLock();
	}
#pragma omp barrier
	return clhAbortablelock;
}

#define UNDERLYING_LOCK CLHAbortableLock

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
