
#include <stdlib.h>
#include <stdint.h>

/*
 *  The Sleator-Tarjan top-down splay algorithm for regular,
 *  single-key trees.
 *
 *  This macro is the body of the splay function.  It rotates the node
 *  containing "key" to the root, if there is one, else the new root
 *  will be an adjacent node (left or right).
 *
 *  The general macro takes 2 comparisons as arguments
 *   [ Frequently, only 1 is necessary, but occasionally, when the keys are
 *   not a primitive data type, the lt and gt operations may not show the
 *   same symmetry as the purely mathematical operations.
 *
 *     lt(a, b)  // defines the "less than" comparison
 *     gt(a, b)  // defines the "greater than" comparison
 *
 *  Nodes in the tree should be a struct with name "type" containing
 *  at least these field names with these types:
 *
 *    lt_field: the field of the key used with "less than" comparisons
 *    gt_field: the field of the key used with "greater than" comparisons
 *
 *    left    : struct type *,
 *    right   : struct type *.
 *
 *   NB: lt_field and gt_field are frequently the same field, but, in general,
 *       they can be different
 *
 *  "root" is a struct type * and is reset to the new root.
 *
 */

#define GENERAL_SPLAY_TREE(type, root, key, lt_field, gt_field, left, right, lt, gt) \
    struct type dummy_node;                                                          \
    struct type *ltree_max, *rtree_min, *yy;                                         \
    if ((root) != NULL) {                                                            \
	ltree_max = rtree_min = &dummy_node;                                         \
	for (;;) {                                                                   \
            if (lt((key), (root)->lt_field)) {                                       \
		if ((yy = (root)->left) == NULL)                                     \
		    break;                                                           \
		if (lt((key), yy->lt_field)) {                                       \
		    (root)->left = yy->right;                                        \
		    yy->right = (root);                                              \
		    (root) = yy;                                                     \
		    if ((yy = (root)->left) == NULL)                                 \
			break;                                                       \
		}                                                                    \
		rtree_min->left = (root);                                            \
		rtree_min = (root);                                                  \
	    } else if (gt((key), (root)->gt_field)) {                                \
		if ((yy = (root)->right) == NULL)                                    \
		    break;                                                           \
		if (gt((key), yy->gt_field)) {                                       \
		    (root)->right = yy->left;                                        \
		    yy->left = (root);                                               \
		    (root) = yy;                                                     \
		    if ((yy = (root)->right) == NULL)                                \
			break;                                                       \
		}                                                                    \
		ltree_max->right = (root);                                           \
		ltree_max = (root);                                                  \
	    } else                                                                   \
		break;                                                               \
	    (root) = yy;                                                             \
	}                                                                            \
	ltree_max->right = (root)->left;                                             \
	rtree_min->left = (root)->right;                                             \
	(root)->left = dummy_node.right;                                             \
	(root)->right = dummy_node.left;                                             \
    }


/*
 *  The Sleator-Tarjan top-down splay algorithm for regular,
 *  single-key trees. This kind of splay tree uses the
 *  builtin < and > as comparison operations, and the lt_field
 *  and gt_field are the same (called 'value' in the derived macro)
 *
 */

#define lcl_builtin_lt(a, b) ((a) < (b))
#define lcl_builtin_gt(a, b) ((a) > (b))

#define REGULAR_SPLAY_TREE(type, root, key, value, left, right)	\
  GENERAL_SPLAY_TREE(type, root, key, value, value, left, right, lcl_builtin_lt, lcl_builtin_gt)

/*
 *  The Sleator-Tarjan top-down splay algorithm for interval trees.
 *
 *  This macro is the body of the splay function.  It rotates the
 *  interval containing "key" to the root, if there is one, else the
 *  new root will be an adjacent interval (left or right).
 *
 *  Nodes in the tree should be a struct with name "type" containing
 *  at least these four field names with these types:
 *
 *    start : same type as key,
 *    end   : same type as key,
 *    left  : struct type *,
 *    right : struct type *.
 *
 *  "root" is a struct type * and is reset to the new root.
 *
 *  Intervals are semi-inclusive: [start, end).
 */

#define lcl_intvl_lt(a, b) ((a) < (b))
#define lcl_intvl_gt(a, b) ((a) >= (b))

#define INTERVAL_SPLAY_TREE(type, root, key, start, end, left, right)	\
  GENERAL_SPLAY_TREE(type, root, key, start, end, left, right, lcl_intvl_lt, lcl_intvl_gt)



struct TraceSplay{
	uint64_t key;
	uint64_t val;
	struct TraceSplay * left;
	struct TraceSplay * right;
};

TraceSplay * volatile gRoot __attribute__((aligned(CACHE_LINE_SIZE)));
uint64_t volatile  gKey __attribute__((aligned(CACHE_LINE_SIZE))) = 64;
volatile bool gTimedOut __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval startTime __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval endTime __attribute__((aligned(CACHE_LINE_SIZE)));

    static inline struct TraceSplay* splay(struct TraceSplay* root, uint64_t ip) {
        REGULAR_SPLAY_TREE(TraceSplay, root, ip, key, left, right);
        return root;
    }

static inline uint64_t Lookup(uint64_t traceKey){
        TraceSplay* found    = splay(gRoot, traceKey);

        // Check if a trace node with traceKey already exists under this context node
        if(found && (traceKey == found->key)) {
		gRoot = found;
		return found->val;
        } else {
            TraceSplay* newNode = new TraceSplay();
            newNode->key = traceKey;
            newNode->val = 0;
            if(!found) {
                newNode->left = NULL;
                newNode->right = NULL;
            } else if(traceKey < found->key) {
                newNode->left = found->left;
                newNode->right = found;
                found->left = NULL;
            } else { // addr > addr of found
                newNode->left = found;
                newNode->right = found->right;
                found->right = NULL;
            }
            gRoot = newNode;
	    return 0;
        }
}

static inline void Populate(uint64_t numkeys){
        int a[numkeys];
        for(int i = 0; i < numkeys ; i++)
            a[i] = i;

        // jumble
        srand(0);
        for(int i = 0; i < numkeys ; i++) {
            int randIndex = rand() % numkeys;
            int  tmp =  a[randIndex];
            a[randIndex] = a[i];
            a[i] = tmp;
        }
        // insert
        for(int i = 0; i < numkeys ; i++)
            Lookup(i);
}
#if 0
static inline uint64_t Worker(UNDERLYING_LOCK * LockType * hmcs, uint64_t numOps ){
   unsigned int seed;
   uint64_t key;
   QNode me;
   uint64_t i=0;
   for(i = 0; i < numOps && !gTimedOut; i++){
       int n = rand_r(&seed);
       int8_t bias = n  & 31;
       switch(bias){
         case 1: case 2: case 3: 
            key = gKey -bias; 
            break;
         case 4: case 5: case 6:
            // bias
            key = gKey + bias - 3;
            break;
         default:
            // common case;
            key = gKey;
       }
       hmcs->Acquire(&me);
       Lookup(key);
       hmcs->Release(&me);
   }
   return i;
}
#else
static inline void Worker(UNDERLYING_LOCK * hmcs, uint64_t numOps, int64_t waitThreshold,  uint64_t &executedIters, uint64_t &numSuccessfulAcquisitions){
   unsigned int seed;
   uint64_t key;
   uint64_t i=0;
   uint64_t next = rand_r(&seed) % 10;
   uint64_t nextRoundup = 10;
   for(i = 0; i < numOps && !gTimedOut; i++){
       int n = rand_r(&seed);
       if(i  == next) {
           nextRoundup += 10;   
           next =  nextRoundup + n % 10;


#ifdef  PHASE_BEHAVIOR
          // in phase behavior if key is odd we have 100% hit else 90% hit to support TSX better
	   if(gKey & 1) { 
	    key = gKey;
           } else {
#endif
           int8_t bias = n  & 31;
           if( i & 1)
               key = gKey-bias;
           else
               key = gKey+bias;
#ifdef  PHASE_BEHAVIOR
           }
#endif

       }else
            key = gKey;
       int64_t patience = GetFastClockTick() + waitThreshold;

       if(hmcs->Acquire(patience) == true) {
       	    Lookup(key);
       	    hmcs->Release(patience);
	    numSuccessfulAcquisitions++;
       }
   }
   executedIters = i;
}
#endif

struct sigevent gSev;
timer_t gTimerid;
#define REALTIME_SIGNAL       (SIGRTMIN + 3)
#define errExit(msg)    do { perror(msg); exit(EXIT_FAILURE);} while (0)

#define PERIODIC_TIMER_SEC (1)
uint64_t gFinalTimeout;

#define MAX_SPLAY_TREE_KEYS (8 * 1024)

void StartTimer(uint64_t timeoutSec){
    struct itimerspec its;
    /* Start the timer */
    its.it_value.tv_sec = PERIODIC_TIMER_SEC;
    gFinalTimeout = timeoutSec;
    its.it_value.tv_nsec = 0;
    its.it_interval.tv_sec = PERIODIC_TIMER_SEC;
    its.it_interval.tv_nsec = 0;

    if (timer_settime(gTimerid, 0, &its, NULL) == -1)
    errExit("timer_settime");
}

static void TimeoutHandler(int sig, siginfo_t* siginfo, void* p){
static int hits = 0;
    if(hits == gFinalTimeout){
     // Stop timer and tell all threads to quit.
    gTimedOut = true;
    COMMIT_ALL_WRITES();
    gettimeofday(&endTime, 0);
    // disarm timer

    struct itimerspec its;
    /* Start the timer */
    its.it_value.tv_sec = 0;
    its.it_value.tv_nsec = 0;
    its.it_interval.tv_sec = 0;
    its.it_interval.tv_nsec = 0;
    if (timer_settime(gTimerid, 0, &its, NULL) == -1)
    errExit("timer_settime");
    return;
   }
   hits++;

    // set a random number between 0+Bias - MaxKey-Bias
    int n = rand() % MAX_SPLAY_TREE_KEYS;
    if (n < 31)
       n = 31;
    else if (n > MAX_SPLAY_TREE_KEYS - 32)
       n = MAX_SPLAY_TREE_KEYS - 32;

    gKey = n;
}

static void CreateTimer(){

    // the man pages cite sigev_notify_thread_id in struct sigevent,
    // but often the only name is a hidden union name.
#ifndef sigev_notify_thread_id
#define sigev_notify_thread_id  _sigev_un._tid
#endif

    memset(&gSev, 0, sizeof(struct sigevent));
    gSev.sigev_notify = SIGEV_THREAD_ID;
    gSev.sigev_signo = REALTIME_SIGNAL;
    gSev.sigev_value.sival_ptr = &gTimerid;
    gSev.sigev_notify_thread_id = syscall(SYS_gettid);
    clockid_t clock = CLOCK_REALTIME;
    int ret = timer_create(clock, &gSev, &gTimerid);
    assert(ret == 0);

    /* Establish handler for timer signal */
    //printf("Establishing handler for signal %d\n", REALTIME_SIGNAL);
    struct sigaction sa;
    sa.sa_flags = SA_SIGINFO;
    sa.sa_sigaction = TimeoutHandler;
    sigemptyset(&sa.sa_mask);
    if (sigaction(REALTIME_SIGNAL, &sa, NULL) == -1)
    errExit("sigaction");
}

using namespace std;

int main(int argc, char *argv[]){
    uint64_t timeoutSec = atol(argv[1]);
    uint64_t totalIters = atol(argv[2]);
    int64_t waitThreshold = atol(argv[3]);
    int64_t numAborters = atol(argv[4]);
    int numThreads = atoi(argv[5]); /**** NOTE THIS TEST NEEDS TO BE RUN WITH ALL THREADS and CONTROL NUMBER OF ABORTERS ***/
    int levels = atoi(argv[6]);
    int * participantsAtLevel = (int * ) malloc(sizeof(int) * levels);
    thresholdAtLevel = (int * ) malloc(sizeof(int) * levels);
    cout<<"\n timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" waitThreshold="<<waitThreshold<<" numAborters="<< numAborters<< " numThreads="<<numThreads<<" levels="<<levels<<" ";
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[7 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[7 + 2*i + 1]);
        cout<<" n"<<i+1<<"="<<participantsAtLevel[i]<<" t"<<i+1<<"="<<thresholdAtLevel[i];
    }
    cout<<endl;


    // initalize
    gTimedOut = false;

    omp_set_num_threads(numThreads);
    uint64_t elapsed;
    uint64_t totalExecutedIters = 0;
    uint64_t totalSuccessfulIters = 0;

    Populate(MAX_SPLAY_TREE_KEYS);


    // Set up alarm after 3 minutes to time out
    //signal(SIGALRM, AlarmHandler);
    //alarm(ALARM_TIME);
    CreateTimer();


#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        uint64_t myIters=0;
        uint64_t mySuccessfulAcquisitions=0;
        uint64_t numIter = totalIters / numThreads;
        int64_t myWaitThreshold = 1000000000000L;
        struct drand48_data randSeedbuffer;
        srand48_r(tid, &randSeedbuffer);

#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif
        UNDERLYING_LOCK * hmcs = LockInit(tid, size, levels, participantsAtLevel);

        // Choose myWaitThreshold for the threads that abort
        assert(numAborters <= numThreads);
        if(numAborters > 0){
        	int mod = numThreads/numAborters;
		if(tid % mod == 0) {
			// I am an aborter
			myWaitThreshold = waitThreshold;
		}
	}


#pragma omp barrier
        // reset myIters
        myIters = 0;
        // reset mySuccessfulAcquisitions
        mySuccessfulAcquisitions=0;
        //printf("\n %d part", tid);

        if(tid == 0) {
            StartTimer(timeoutSec);
            gettimeofday(&startTime, 0);
        }
        Worker(hmcs, numIter, myWaitThreshold, myIters, mySuccessfulAcquisitions);

    DONE:
        // If timed out, let us add add total iters executed
        if(gTimedOut){
            ATOMIC_ADD(&totalExecutedIters, myIters);
        }
        ATOMIC_ADD(&totalSuccessfulIters, mySuccessfulAcquisitions);
    }

    // If not timed out, let us get the end time and total iters
    if(!gTimedOut){
        gettimeofday(&endTime, 0);
        totalExecutedIters = (totalIters);
    } else {
        std::cout<<"\n Timed out";
        // All except thread 0 (signal received) will report 1 trip extra
        // If each thread performs 1K iters, it is a small .1% skid. So ignore.
    }


    elapsed = TIME_SPENT(startTime, endTime);
    double throughPut = (totalExecutedIters) * 1000000.0 / elapsed;
    double throughPutSuccessfulAcq = (totalSuccessfulIters) * 1000000.0 / elapsed;
    std::cout<<"\n elapsed = " << elapsed;
    std::cout<<"\n totalExecutedIters = " << totalExecutedIters;
    std::cout<<"\n totalSuccessfulIters = " << totalSuccessfulIters << "\n";
    std::cout<<"\n throughPut = " << throughPut << "\n";
    std::cout<<"\n throughPutSuccessfulAcq = " << throughPutSuccessfulAcq << "\n";

    return 0;
}

