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
 

  typedef enum {available, leaving, transient, waiting, recycled} qnode_status;
  struct mcs_nb_qnode {
      struct mcs_nb_qnode *volatile prev __attribute__((aligned(CACHE_LINE_SIZE)));
      struct mcs_nb_qnode *volatile next __attribute__((aligned(CACHE_LINE_SIZE)));
      volatile qnode_status status __attribute__((aligned(CACHE_LINE_SIZE)));
      char buf[CACHE_LINE_SIZE-sizeof(qnode_status)];

  } __attribute__((aligned(CACHE_LINE_SIZE)));
  struct mcs_nb_lock{
      mcs_nb_qnode *volatile tail __attribute__((aligned(CACHE_LINE_SIZE)));
      mcs_nb_qnode *lock_holder __attribute__((aligned(CACHE_LINE_SIZE)));     // node allocated by lock holder
      char buf[CACHE_LINE_SIZE-sizeof(mcs_nb_qnode *)];
      mcs_nb_lock(): tail(0), lock_holder(0){}
  } __attribute__((aligned(CACHE_LINE_SIZE)));
  
  typedef struct local_qnode {
      union {
//          clh_nb_qnode cnq;           // members of this union are
          mcs_nb_qnode mnq;           // never accessed by name
      } real_qnode;
      volatile bool allocated __attribute__((aligned(CACHE_LINE_SIZE)));
      struct local_qnode *next_in_pool __attribute__((aligned(CACHE_LINE_SIZE)));
      char buf[CACHE_LINE_SIZE-sizeof(struct local_qnode *)];
  } local_qnode;
  
  typedef struct {
      local_qnode *try_this_one __attribute__((aligned(CACHE_LINE_SIZE)));     // pointer into circular list
      char buf[CACHE_LINE_SIZE-sizeof(local_qnode *)];
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

  
  #define AVAILABLE ((mcs_nb_qnode *) 1)
  #define LEAVING   ((mcs_nb_qnode *) 2)
  #define TRANSIENT ((mcs_nb_qnode *) 3)
      // Thread puts TRANSIENT in its next pointer and, if possible, transient
      // in its successor's status word, when it wants to leave but was unable
      // to break the link to it from its precedessor.
 
  #define swap(a,b) SWAP(a,b) 
  #define compare_and_store(a, b, c) BOOL_CAS(a,b,c)
  #define mqn_swap(p,v) (mcs_nb_qnode *) \
      swap((volatile unsigned long *) (p), (unsigned long) (v))
  #define s_swap(p,v) (qnode_status) \
      swap((volatile unsigned long *) (p), (unsigned long) (v))
  
  #define my_head_node_ptr() (&me)
  #define alloc_qnode() (mcs_nb_qnode *) alloc_local_qnode(my_head_node_ptr())
  #define free_qnode(p) free_local_qnode((local_qnode *) p)

  
 

struct MCSNBAbortableLock{
  mcs_nb_lock gLock  __attribute__((aligned(CACHE_LINE_SIZE)));

  MCSNBAbortableLock(): gLock() {}
  bool Acquire(int64_t T) {
  {
      mcs_nb_lock * L = &gLock;
      mcs_nb_qnode *I = alloc_qnode();
      mcs_nb_qnode *pred_next;
  
      I->next = 0;
      mcs_nb_qnode *pred = mqn_swap(&L->tail, I);
      if (!pred) {
          L->lock_holder = I;
          return true;
      }
  
      I->status = waiting;
      while (1) {
          pred_next = mqn_swap(&pred->next, I);
          /* If pred_next is not nil then my predecessor tried to leave or
              grant the lock before I was able to tell it who I am.  Since it
              doesn't know who I am, it won't be trying to change my status
              word, and since its CAS on the tail pointer, if any, will have
              failed, it won't have reclaimed its own qnode, so I'll have to. */
          if (pred_next == AVAILABLE) {
              L->lock_holder = I;
              free_qnode(pred);
              return true;
          } else if (!pred_next) {
              while (1) {
                  if (GetFastClockTick() > T) {
                      goto timeout1;
                  }
                  qnode_status stat = I->status;
                  if (stat == available) {
                      L->lock_holder = I;
                      free_qnode(pred);
                      return true;
                  } else if (stat == leaving) {
                      mcs_nb_qnode *new_pred = pred->prev;
                      free_qnode(pred);
                      pred = new_pred;
                      I->status = waiting;
                      break;  // exit inner loop; continue outer loop
                  } else if (stat == transient) {
                      mcs_nb_qnode *new_pred = pred->prev;
                      if (s_swap(&pred->status, recycled) != waiting) {
                          free_qnode(pred);
                      } /* else when new predecessor changes this to available,
                          leaving, or transient it will find recycled, and will
                          reclaim old predecessor's node. */
                      pred = new_pred;
                      I->status = waiting;
                      break;  // exit inner loop; continue outer loop
                  } // else stat == waiting; continue inner loop
              }
          } else if (GetFastClockTick() > T) {
              goto timeout2;
          } else if (pred_next == LEAVING) {
              mcs_nb_qnode *new_pred = pred->prev;
              free_qnode(pred);
              pred = new_pred;
          } else if (pred_next == TRANSIENT) {
              mcs_nb_qnode *new_pred = pred->prev;
              if (s_swap(&pred->status, recycled) != waiting) {
                  free_qnode(pred);
              } /* else when new predecessor changes this to available,
                   leaving, or transient it will find recycled, and will
                   reclaim old predecessor's node. */
              pred = new_pred;
          }
      }
  
      timeout1: {
          I->prev = pred;
          if (compare_and_store(&pred->next, I, 0)) {
              // predecessor doesn't even know I've been here
              mcs_nb_qnode *succ = mqn_swap(&I->next, LEAVING);
              if (succ) {
                  if (s_swap(&succ->status, leaving) == recycled) {
                      /* Timing window: successor already saw my modified
                          next pointer and declined to modify it.  Nobody is
                          going to look at my successor node, but they will
                          see my next pointer and know what happened. */
                      free_qnode(succ);
                  } /* else successor will reclaim me when it sees my
                      change to its status word. */
              } else {
                  // I don't seem to have a successor.
                  if (compare_and_store(&L->tail, I, pred)) {
                      free_qnode(I);
                  } /* else a newcomer hit the timing window or my successor
                      is in the process of leaving.  Somebody will discover
                      I'm trying to leave, and will free my qnode for me. */
              }
          } else {
              /* Predecessor is trying to leave or to give me (or somebody)
                  the lock.  It has a pointer to my qnode, and is planning
                  to use it.  I can't wait for it to do so, so I can't free
                  my own qnode. */
              mcs_nb_qnode *succ = mqn_swap(&I->next, TRANSIENT);
              if (succ) {
                  if (s_swap(&succ->status, transient) == recycled) {
                      /* Timing window: successor already saw my modified
                          next pointer and declined to modify it.  Nobody is
                          going to look at my successor node, but they will see
                          my next pointer and know what happened. */
                      free_qnode(succ);
                  } /* else successor will reclaim me when it sees my
                      change to its status word. */
              } /* else I don't seem to have a successor, and nobody can
                  wait for my status word to change.  This is the
                  pathological case where we can temporarily require
                  non-linear storage. */
          }
          return false;
      }
  
      timeout2: {
          /* pred_next is LEAVING or TRANSIENT; pred->next is I.
              Put myself in transient state, so some successor can
              eventually clean up. */
          mcs_nb_qnode *succ;
          /* put predecessor's next field back, as it would be if I
              had timed out in the inner while loop and been unable to
              update predecessor's next pointer: */
          pred->next = pred_next;
          I->status = (pred_next == LEAVING ? leaving : transient);
          I->prev = pred;
          succ = mqn_swap(&I->next, TRANSIENT);
          if (succ) {
              if (s_swap(&succ->status, transient) == recycled) {
                  /* Timing window: successor already saw my modified next
                      pointer and declined to modify it.  Nobody is going
                      to look at my successor node, but they will see my
                      next pointer and know what happened. */
                  free_qnode(succ);
              } /* else successor will reclaim me when it sees my change
                  to its status word. */
          } /* else I don't seem to have a successor, and nobody can wait
              for my status word to change.  This is the pathological case
              where we can temporarily require non-linear storage. */
          return false;
      }
  }
  
  }
  
  void Release(int64_t T) {
      mcs_nb_lock *L = &gLock;
      mcs_nb_qnode *I = L->lock_holder;
      mcs_nb_qnode *succ = mqn_swap(&I->next, AVAILABLE);
      /* As a general rule, I can't reclaim my own qnode on release because
          my successor may be leaving, in which case somebody is going to
          have to look at my next pointer to realize that the lock is
          available.  The one exception (when I *can* reclaim my own node)
          is when I'm able to change the lock tail pointer back to nil. */
      if (succ) {
          if (s_swap(&succ->status, available) == recycled) {
              /* Timing window: successor already saw my modified next
                  pointer and declined to modify it.  Nobody is going to
                  look at my successor node, but they will see my next
                  pointer and know what happened. */
              free_qnode(succ);
          } /* else successor (old or new) will reclaim me when it sees my
              change to the old successor's status word. */
      } else {
          // I don't seem to have a successor.
          if (compare_and_store(&L->tail, I, 0)) {
              free_qnode(I);
          } /* else a newcomer hit the timing window or my successor is in
              the process of leaving.  Somebody will discover I'm giving
              the lock away, and will free my qnode for me. */
      }
  }
};


MCSNBAbortableLock * mcsnbAbortablelock;
MCSNBAbortableLock * LockInit(int tid, int maxThreads, int levels, int * participantsAtLevel){
#pragma omp barrier

me.try_this_one = &me.initial_qnode;
me.initial_qnode.allocated = false;
me.initial_qnode.next_in_pool = &me.initial_qnode;


#pragma omp single
	{
		mcsnbAbortablelock = new MCSNBAbortableLock();
	}
#pragma omp barrier
	return mcsnbAbortablelock;
}

#define UNDERLYING_LOCK MCSNBAbortableLock

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
