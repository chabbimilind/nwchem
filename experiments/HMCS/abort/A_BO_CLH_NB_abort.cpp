#include "util.h" 
  
int * thresholdAtLevel;

 // Code to manage a local but shared pool of qnodes.
  // All nodes are allocated by, and used by, a given thread, and may
  // reside in local memory on an ncc-numa machine.  The nodes belonging
  // to a given thread form a circular singly linked list.  The head
  // pointer points to the node most recently successfully allocated.
  // A thread allocates from its own pool by searching forward from the
  // pointer for a node that's marked "unused".  A thread (any thread)
  // deallocates a node by marking it "unused".
 

  struct clh_nb_qnode {
      struct clh_nb_qnode *volatile prev __attribute__((aligned(CACHE_LINE_SIZE)));
      char buf[CACHE_LINE_SIZE-sizeof(struct clh_nb_qnode *)];
  };
  struct clh_nb_lock{
      clh_nb_qnode *volatile tail __attribute__((aligned(CACHE_LINE_SIZE)));
      clh_nb_qnode *lock_holder __attribute__((aligned(CACHE_LINE_SIZE)));   // node allocated by lock holder
      char buf[CACHE_LINE_SIZE-sizeof(clh_nb_qnode *)];
      clh_nb_lock() : tail(0), lock_holder(0){}   
  };
  
  //#define AVAILABLE ((clh_nb_qnode *) 1)
  #define GLOBAL_RELEASE ((clh_nb_qnode *) 0b10)
  #define GLOBAL_RELEASE_I (0b10)
  #define LOCAL_RELEASE ((clh_nb_qnode *) 0b01)
  #define LOCAL_RELEASE_I (0b01)
  #define SUCCESSOR_ABORTED ((clh_nb_qnode *) 0b100)
  #define SUCCESSOR_ABORTED_I (0b100)
  #define SET_ABORTED(x) (x|0b100)
  #define IS_SUCC_ABORTED(x) (x&0b100)
  #define INITIAL_STATE ((clh_nb_qnode *) 0)
  #define INITIAL_STATE_I (0)
  
  #define swap(a,b) SWAP(a,b) 
  #define cas(a, b, c) CAS(a,b,c)
  #define cqn_swap(p,v) (clh_nb_qnode *) \
      swap((volatile unsigned long*) (p), (unsigned long) (v))
  #define compare_and_store(p,o,n) \
      (cas((volatile unsigned long *) (p), \
           (unsigned long) (o), (unsigned long) (n)) \
              == (unsigned long) (o))

  #define my_head_node_ptr() (&me) 
  #define alloc_qnode() (clh_nb_qnode *) alloc_local_qnode(my_head_node_ptr())
  #define free_qnode(p) free_local_qnode((local_qnode *) p)
  
  typedef struct local_qnode {
      union {
          clh_nb_qnode cnq;           // members of this union are
//          mcs_nb_qnode mnq;           // never accessed by name
      } real_qnode;
      volatile bool allocated __attribute__((aligned(CACHE_LINE_SIZE)));
      struct local_qnode *next_in_pool __attribute__((aligned(CACHE_LINE_SIZE)));
      char buf[CACHE_LINE_SIZE-sizeof(struct local_qnode *)];
  } local_qnode;
  
  typedef struct {
      local_qnode *try_this_one;     // pointer into circular list
      local_qnode initial_qnode;
  } local_head_node;
  
__thread local_head_node me;

  inline local_qnode *alloc_local_qnode(local_head_node *hp)
  {
      local_qnode *p = hp->try_this_one;
      if (!p->allocated) {
          p->allocated = true;
          return p;
      } else {
          local_qnode *q = p->next_in_pool;
          while (q != p) {
              if (!q->allocated) {
                  hp->try_this_one = q;
                  q->allocated = true;
                  return q;
              } else {
                  q = q->next_in_pool;
              }
          }
          // All qnodes are in use.  Allocate new one and link into list.
          q = (local_qnode *) malloc(sizeof(local_qnode));
          q->next_in_pool = p->next_in_pool;
          p->next_in_pool = q;
          hp->try_this_one = q;
          q->allocated = true;
          return q;
      }
  }
  
  #define free_local_qnode(p) ((p)->allocated = false)

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

volatile int y = 0;
struct A_C_BO_CLHLock{
  const uint64_t maxThreshold = 64;
  clh_nb_lock gLock  __attribute__((aligned(CACHE_LINE_SIZE)));
  uint64_t curThreshold __attribute__((aligned(CACHE_LINE_SIZE)));
  char buf[CACHE_LINE_SIZE-sizeof(uint64_t)];

  A_C_BO_CLHLock(): gLock()  {curThreshold=maxThreshold;  }
  inline bool Acquire(int64_t T) {
      clh_nb_lock * L = &gLock;
       clh_nb_qnode *I = alloc_qnode();
  
      I->prev = INITIAL_STATE;
      clh_nb_qnode * pred = cqn_swap(&L->tail, I);
      if (!pred) {
          // lock was free and uncontested; just return
          L->lock_holder = I;
                  if (abLock.Acquire(T))
                        return true;
                  ReleaseLocalOnly();
                  return false;
      }

clh_nb_qnode * volatile pred_pred = 0;
      do {
RETRY:
          pred_pred = pred->prev;

          switch((uint64_t)pred_pred){
		case INITIAL_STATE_I:
			break;
		case SUCCESSOR_ABORTED_I:
			// CAS back SUCCESOR NOT ABORTED
			CAS(&(pred->prev), SUCCESSOR_ABORTED, INITIAL_STATE);
			break;
		case LOCAL_RELEASE_I: {
              		L->lock_holder = I;
              		free_qnode(pred);
              		return true;
			}
		case GLOBAL_RELEASE_I: {
          	  L->lock_holder = I;
          	  free_qnode(pred);
          	  if (abLock.Acquire(T))
                  	return true;
        	  ReleaseLocalOnly();
	          return false;
		}
                default : //(pred_pred) 
                {
                    free_qnode(pred);
                    pred = pred_pred;
		    // can't abort right away ...
		    continue;
                }
      	 }
      } while(GetFastClockTick()< T);
 
      // set pred's successor aborted to true
      //clh_nb_qnode *x = SET_ABORTED(pred_pred);
      if(BOOL_CAS(&(pred->prev), pred_pred, SUCCESSOR_ABORTED) == false) {
	goto RETRY;
      }
  
      // timed out; reclaim or abandon own node
  
      if (compare_and_store(&L->tail, I, pred)) {
          // last process in line
          free_qnode(I);
      } else {
          I->prev = pred;
      }
      return false; 
  }
/*
inline bool Acquire(int64_t T)
{
	if(AcquireReal(T)) {
		int x = ++y;
		assert(x==y);
		y--;
		return true;
	}
	return false;
}
*/
   inline void ReleaseLocalOnly() {
      clh_nb_lock *L = &gLock;

      clh_nb_qnode *I = L->lock_holder;
      if (compare_and_store(&L->tail, I, 0)) {
          // no competition for lock; reclaim qnode
          free_qnode(I);
      } else {
          I->prev = GLOBAL_RELEASE;
      }
  }

  inline void Release(int64_t T) {
      clh_nb_lock *L = &gLock;
      clh_nb_qnode *I = L->lock_holder;
      curThreshold--;
      clh_nb_qnode * releaseVal;
      if((curThreshold != 0) && (L->tail != I) &&  (I->prev == INITIAL_STATE) ){
        // try to CAS LOCAL_RELEASE
         if(BOOL_CAS(&(I->prev), INITIAL_STATE, LOCAL_RELEASE) == true)
		return;
      }
         
	// release glock
        

	abLock.Release(T);
        curThreshold = maxThreshold;
	releaseVal=GLOBAL_RELEASE;

      if (compare_and_store(&L->tail, I, 0)) {
          // no competition for lock; reclaim qnode
          free_qnode(I);
      } else {
          I->prev = releaseVal;
      }
  }
};



A_C_BO_CLHLock  ** lockLocations __attribute__((aligned(CACHE_LINE_SIZE)));

A_C_BO_CLHLock* LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
    // Total locks needed = participantsPerLevel[1] + participantsPerLevel[2] + .. participantsPerLevel[levels-1] + 1


assert(levels==2); // that is the only design now...

    int totalLocksNeeded = 0;
    for (int i=0; i < levels; i++) {
        totalLocksNeeded += maxThreads / participantsAtLevel[i] ;
    }


#pragma omp barrier

me.try_this_one = &me.initial_qnode;
me.initial_qnode.allocated = false;
me.initial_qnode.next_in_pool = &me.initial_qnode;


#pragma omp single
    {
        //lockLocations = new HNode*[totalLocksNeeded];
        // use memalign for alignemnt new does not ensure alignment
        lockLocations = (A_C_BO_CLHLock**)memalign(CACHE_LINE_SIZE, sizeof(A_C_BO_CLHLock*) * totalLocksNeeded);
    }

    // Lock at curLevel l will be initialized by a designated master

    int lastLockLocationEnd = 0;
    int curLevel = 0; 
        if (tid%participantsAtLevel[curLevel] == 0) {
            // master, initialize the lock
            int lockLocation = lastLockLocationEnd + tid/participantsAtLevel[curLevel];
            lastLockLocationEnd += maxThreads/participantsAtLevel[curLevel];
            A_C_BO_CLHLock * curLock = new A_C_BO_CLHLock();
            lockLocations[lockLocation] = curLock;
        }
#pragma omp barrier
    // return the lock to each thread
    return lockLocations[tid/participantsAtLevel[0]];
}





#define UNDERLYING_LOCK A_C_BO_CLHLock

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
