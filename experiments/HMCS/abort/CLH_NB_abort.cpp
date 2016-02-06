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
 

  typedef struct clh_nb_qnode {
      struct clh_nb_qnode *volatile prev __attribute__((aligned(CACHE_LINE_SIZE)));
  } clh_nb_qnode;
  struct clh_nb_lock{
      clh_nb_qnode *volatile tail __attribute__((aligned(CACHE_LINE_SIZE)));
      clh_nb_qnode *lock_holder __attribute__((aligned(CACHE_LINE_SIZE)));   // node allocated by lock holder
      clh_nb_lock() : tail(0), lock_holder(0){}   
  };
  
  #define AVAILABLE ((clh_nb_qnode *) 1)
  
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

 

struct CLHNBAbortableLock{
  clh_nb_lock gLock  __attribute__((aligned(CACHE_LINE_SIZE)));
  CLHNBAbortableLock(): gLock() {}
  bool Acquire(int64_t T) {
      clh_nb_lock * L = &gLock;
       clh_nb_qnode *I = alloc_qnode();
  
      I->prev = 0;
      clh_nb_qnode * pred = cqn_swap(&L->tail, I);
      if (!pred) {
          // lock was free and uncontested; just return
          L->lock_holder = I;
          return true;
      }
      
      if (pred->prev == AVAILABLE) {
          // lock was free; just return
          L->lock_holder = I;
          free_qnode(pred);
          return true;
      }
  
      while (GetFastClockTick()< T) {
          clh_nb_qnode *pred_pred = pred->prev;
          if (pred_pred == AVAILABLE) {
              L->lock_holder = I;
              free_qnode(pred);
              return true;
          } else if (pred_pred) {
              free_qnode(pred);
              pred = pred_pred;
          }
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
  
  void Release(int64_t T) {
      clh_nb_lock *L = &gLock;
      clh_nb_qnode *I = L->lock_holder;
      if (compare_and_store(&L->tail, I, 0)) {
          // no competition for lock; reclaim qnode
          free_qnode(I);
      } else {
          I->prev = AVAILABLE;
      }
  }
};


CLHNBAbortableLock * clhnbAbortablelock;
CLHNBAbortableLock * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
#pragma omp barrier

me.try_this_one = &me.initial_qnode;
me.initial_qnode.allocated = false;
me.initial_qnode.next_in_pool = &me.initial_qnode;


#pragma omp single
	{
		clhnbAbortablelock = new CLHNBAbortableLock();
	}
#pragma omp barrier
	return clhnbAbortablelock;
}

#define UNDERLYING_LOCK CLHNBAbortableLock

#ifdef SPLAY_TREE_DRIVER
#include "splay_driver.cpp"
#elif defined(CONTROLLED_NUMBER_OF_ABORTERS)
#include "splay_driver_few_aborters.cpp"
#else
#include "abort_driver.cpp"
#endif
