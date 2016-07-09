
#include <stdlib.h>
#include <stdint.h>

uint64_t volatile  gKey __attribute__((aligned(CACHE_LINE_SIZE))) = 64;
volatile bool gTimedOut __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval startTime __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval endTime __attribute__((aligned(CACHE_LINE_SIZE)));
char dummyDummy[CACHE_LINE_SIZE-sizeof(struct timeval)];


static inline void Worker(UNDERLYING_LOCK * hmcs, uint64_t numOps, int64_t waitThreshold,  
   uint64_t &executedIters, uint64_t &numSuccessfulAcquisitions,
   uint64_t &acquireCost,
   uint64_t &releaseCost,
   uint64_t &abortCost) {
   uint64_t t1, t2, t3, t4, t5, t6, t7, outsideStart;

   //t1 = GetFastClockTick();
   uint64_t i=0;
   for(i = 0; i < numOps && !gTimedOut; i++){
       t2 = GetFastClockTick();
       int64_t patience = t2 + waitThreshold;
       if(hmcs->Acquire(patience) == true) {
            t3 = GetFastClockTick();
            //t4 = GetFastClockTick();
       	    hmcs->Release(patience);
            t5 = GetFastClockTick();
	    numSuccessfulAcquisitions++;
            acquireCost += t3 - t2;
            releaseCost += t5 - t3;
       } else {
            t6 = GetFastClockTick();
            abortCost += t6 - t2;
       }
       
   }
   //t7 = GetFastClockTick(); 
   //nonCSWork += t7 - t1 - (csWork + acquireCost + releaseCost + abortCost);
   executedIters = i;
}

struct sigevent gSev;
timer_t gTimerid;
#define REALTIME_SIGNAL       (SIGRTMIN + 3)
#define errExit(msg)    do { perror(msg); exit(EXIT_FAILURE);} while (0)

void StartTimer(uint64_t timeoutSec){
    struct itimerspec its;
    /* Start the timer */
    its.it_value.tv_sec = timeoutSec;
    its.it_value.tv_nsec = 0;
    its.it_interval.tv_sec = 0;
    its.it_interval.tv_nsec = 0;

    if (timer_settime(gTimerid, 0, &its, NULL) == -1)
        errExit("timer_settime");
}

static void TimeoutHandler(int sig, siginfo_t* siginfo, void* p){
    // Stop timer and tell all threads to quit.
    gTimedOut = true;
    COMMIT_ALL_WRITES();
    gettimeofday(&endTime, 0);
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
    uint64_t mustBeAMultile = atol(argv[1]);
    uint64_t timeoutSec = atol(argv[2]);
    uint64_t totalIters = atol(argv[3]);
    int64_t waitThreshold = atol(argv[4]);
    int numThreads = atoi(argv[5]);
    int activeThreads = atoi(argv[6]);
    int levels = atoi(argv[7]);
    int * participantsAtLevel = (int * ) malloc(sizeof(int) * levels);
    thresholdAtLevel = (int * ) malloc(sizeof(int) * levels);
    cout<<"\n mustBeAMultile="<<mustBeAMultile <<" timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" waitThreshold="<<waitThreshold<<" numThreads="<<numThreads<<" levels="<<levels<<" ";
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[8 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[8 + 2*i + 1]);
        cout<<" n"<<i+1<<"="<<participantsAtLevel[i]<<" t"<<i+1<<"="<<thresholdAtLevel[i];
    }
    cout<<endl;

    struct Metrics {
        uint64_t totalNonCSWork __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalCSWork __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalAcquireCost __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalReleaseCost __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalAbortCost __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalExecutedIters __attribute__((aligned(CACHE_LINE_SIZE)));
        uint64_t totalSuccessfulIters __attribute__((aligned(CACHE_LINE_SIZE)));
        char buf[CACHE_LINE_SIZE - sizeof(uint64_t)];
	Metrics() : totalSuccessfulIters(0), totalNonCSWork(0), totalCSWork(0), totalAcquireCost(0), totalReleaseCost(0), totalAbortCost(0), totalExecutedIters(0)  {}
     };

    Metrics metrics;

    // initalize
    gTimedOut = false;

    omp_set_num_threads(numThreads);
    uint64_t elapsed;

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
        uint64_t nonCSWork = 0;
        uint64_t csWork = 0;
        uint64_t acquireCost = 0;
        uint64_t releaseCost = 0;
        uint64_t abortCost = 0; 

        uint64_t numIter = totalIters / numThreads;
        struct drand48_data randSeedbuffer;
        srand48_r(tid, &randSeedbuffer);

#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif
        UNDERLYING_LOCK * hmcs = LockInit(tid, size, levels, participantsAtLevel);

#pragma omp barrier
        // reset myIters
        myIters = 0;
        // reset mySuccessfulAcquisitions
        mySuccessfulAcquisitions=0;
        if(tid % mustBeAMultile !=0 || tid >= activeThreads)
            goto DONE;
        //printf("\n %d part", tid);


        if(tid == 0) {
            StartTimer(timeoutSec);
            gettimeofday(&startTime, 0);
        }
  
        Worker(hmcs, numIter, waitThreshold, myIters, mySuccessfulAcquisitions, acquireCost, releaseCost, abortCost);

    DONE:
        ATOMIC_ADD(&metrics.totalExecutedIters, myIters);
        ATOMIC_ADD(&metrics.totalSuccessfulIters, mySuccessfulAcquisitions);
#if 1
        ATOMIC_ADD(&metrics.totalNonCSWork, nonCSWork);
        ATOMIC_ADD(&metrics.totalCSWork, csWork);
        ATOMIC_ADD(&metrics.totalAcquireCost, acquireCost);
        ATOMIC_ADD(&metrics.totalReleaseCost, releaseCost);
        ATOMIC_ADD(&metrics.totalAbortCost, abortCost);
#endif
    }
    gettimeofday(&endTime, 0);
    // If not timed out, let us get the end time and total iters
    if(gTimedOut){
        std::cout<<"\n Timed out";
    }


    elapsed = TIME_SPENT(startTime, endTime);
    double throughPut = (metrics.totalExecutedIters) * 1000000.0 / elapsed;
    double throughPutSuccessfulAcq = (metrics.totalSuccessfulIters) * 1000000.0 / elapsed;
    double throughPutAborted = (metrics.totalExecutedIters-metrics.totalSuccessfulIters) * 1000000.0 / elapsed;
#if 1
    double latencySuccessfulAcquisition = 1.0 * (metrics.totalAcquireCost + metrics.totalReleaseCost) / metrics.totalSuccessfulIters;
    double latencySuccessfulAcquisitionPlusAborts = 1.0 *  (metrics.totalAcquireCost + metrics.totalReleaseCost + metrics.totalAbortCost) / metrics.totalSuccessfulIters;
    double latencyAbort = (metrics.totalAbortCost) * 1.0 / (metrics.totalExecutedIters-metrics.totalSuccessfulIters);
    double latencyAcquire= (metrics.totalAcquireCost) * 1.0 / (metrics.totalSuccessfulIters);
    double latencyRelease= (metrics.totalReleaseCost) * 1.0 / (metrics.totalSuccessfulIters);
#endif
    std::cout<<"\n elapsed=" << elapsed;
    std::cout<<"\n totalExecutedIters=" << metrics.totalExecutedIters;
    std::cout<<"\n totalSuccessfulIters=" << metrics.totalSuccessfulIters;
#if 1
    std::cout<<"\n totalAcquireCost=" << metrics.totalAcquireCost;
    std::cout<<"\n totalReleaseCost=" << metrics.totalReleaseCost;
    std::cout<<"\n totalAbortCost=" << metrics.totalAbortCost;
#endif
    std::cout<<"\n throughPut=" << throughPut;
    std::cout<<"\n throughPutSuccessfulAcq=" << throughPutSuccessfulAcq;
    std::cout<<"\n throughPutAborted=" << throughPutAborted;
#if 1
    std::cout<<"\n latencySuccessfulAcquisition=" << latencySuccessfulAcquisition;
    std::cout<<"\n latencySuccessfulAcquisitionPlusAborts=" << latencySuccessfulAcquisitionPlusAborts;
    std::cout<<"\n latencyAbort=" << latencyAbort;
    std::cout<<"\n latencyAcquire=" <<latencyAcquire;
    std::cout<<"\n latencyRelease=" << latencyRelease << "\n";
#endif  

    return 0;
}

