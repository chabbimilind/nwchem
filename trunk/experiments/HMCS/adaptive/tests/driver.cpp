//
//
//
//  Created by Milind Chabbi on 4/27/14.
//
//


volatile bool gTimedOut __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval startTime __attribute__((aligned(CACHE_LINE_SIZE)));
struct timeval endTime __attribute__((aligned(CACHE_LINE_SIZE)));


void AlarmHandler(int sig) {
    printf("\n Time out!\n");
    exit(-1);
}


static inline void CriticalSection(){
#ifdef  DOWORK_IN_CS
    DoWorkInsideCS();
#endif
    
#ifdef VALIDATE
    int lvar = var;
    var ++;
    assert(var == lvar + 1);
#endif
}
static inline void OutsideCriticalSection(struct drand48_data * randSeedbuffer){
#ifdef  DOWORK_OUTSIDE_CS
    DoWorkOutsideCS(randSeedbuffer);
#endif
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


#ifdef COMPUTE_LATENCY
#define RUN_LOOP(nIter, level)       do{for(myIters = 0; (myIters < nIter) && (!gTimedOut); myIters++) { \
GET_TICK(myTicksStart);\
hmcs->Acquire(&me); \
CriticalSection();\
hmcs->Release(&me);\
GET_TICK(myTicksEnd);\
myTicksSum += myTicksEnd - myTicksStart;\
OutsideCriticalSection(& randSeedbuffer);\
}}while(0)
#else
#define RUN_LOOP(nIter, level, timeLimit)   GET_TICK(myTicksStart);\
do{for(myIters = 0; (myIters < nIter); myIters++) { \
GET_TICK(myTicksEnd);\
if(myTicksEnd - myTicksStart > timeLimit) break;\
hmcs->Acquire(&me); \
CriticalSection();\
hmcs->Release(&me);\
OutsideCriticalSection(& randSeedbuffer);\
}}while(0)
#endif

using namespace std;

struct CacheLine_t{
    volatile double f1 __attribute__((aligned(CACHE_LINE_SIZE)));
}__attribute__((aligned(CACHE_LINE_SIZE)));



#define NELEMS(x)  (sizeof(x) / sizeof((x)[0]))

int main(int argc, char *argv[]){
    uint64_t mustBeAMultile = atol(argv[1]);
    uint64_t timeoutSec = atol(argv[2]);
    uint64_t totalIters = atol(argv[3]);
    int numThreads = atoi(argv[4]);
    int levels = atoi(argv[5]);
    int * participantsAtLevel = (int * ) malloc(sizeof(int) * levels);
    thresholdAtLevel = (int * ) malloc(sizeof(int) * levels);
    cout<<"\n mustBeAMultile="<<mustBeAMultile <<" timeoutSec="<<timeoutSec<<" totalIters="<<totalIters<<" numThreads="<<numThreads<<" levels="<<levels<<" ";
    for (int i = 0; i <  levels; i++) {
        participantsAtLevel[i] = atoi(argv[6 + 2*i]);
        thresholdAtLevel[i] = atoi(argv[6 + 2*i + 1]);
        cout<<" n"<<i+1<<"="<<participantsAtLevel[i]<<" t"<<i+1<<"="<<thresholdAtLevel[i];
    }
    cout<<endl;
    
    
    // initalize
    gTimedOut = false;
    
    omp_set_num_threads(numThreads);
    uint64_t elapsed;
    uint64_t totalExecutedIters = 0;
    
    // Set up alarm after 3 minutes to time out
    //signal(SIGALRM, AlarmHandler);
    //alarm(ALARM_TIME);
    CreateTimer();
    
#ifdef PROFILE
    // FIX ME.. JUST FOR 3 level lock to get stats
    uint64_t * resultStats1 = new uint64_t[numThreads];
    uint64_t * resultStats2 = new uint64_t[numThreads];
    uint64_t * resultStats3 = new uint64_t[numThreads];
#endif
    
#ifdef COMPUTE_LATENCY
    uint64_t masterTicksSum = 0;
    uint64_t masterIters = 0;
    double * throughPutLatency = new double[numThreads];
#endif
    
    
//    int randomContention [] = {64, 64, 8, 4, 16, 8, 64, 4, 8, 16, 128, 16, 4, 64, 16, 4, 128, 128, 64, 128, 4, 32, 128, 32, 8, 1, 8, 16, 128, 128, 8, 64, 4, 64, 16, 1, 32, 8, 64, 32, 1, 8, 64, 2, 4, 64, 2, 16, 2, 128, 64, 8, 1, 4, 16, 128, 1, 16, 32, 16, 64, 16, 128, 16, 16, 8, 16, 8, 16, 4, 2, 2, 16, 32, 8, 1, 64, 128, 128, 64, 128, 128, 16, 8, 32, 4, 64, 64, 128, 16, 128, 16, 8, 32, 128, 128, 64, 1, 16, 8};
    
    
//    int randomContention [] =  {128, 128, 2, 2, 4, 16, 16, 64, 4, 1, 16, 4, 8, 16, 8, 1, 2, 4, 32, 64, 32, 8, 8, 8, 32, 32, 4, 16, 1, 4, 1, 1, 16, 2, 2, 128, 64, 1, 8, 4, 16, 2, 128, 32, 1, 32, 64, 8, 16, 8, 64, 64, 128, 2, 1, 32, 2, 32, 128, 64, 128, 4, 128, 64};
    
//    int randomContention [] =  {128, 2, 128, 2, 4, 16, 64, 16, 4, 1, 16, 4, 8, 16, 8, 1, 2, 4, 32, 64, 32, 8, 32, 8, 32, 8, 4, 16, 1, 4, 1, 16, 1, 2, 128, 2, 64, 1, 8, 4, 16, 2, 128, 32, 1, 32, 64, 8, 16, 8, 64, 128, 64, 2, 1, 32, 2, 32, 128, 64, 128, 4, 128, 64};
   
    
    int randomContention [] =  {1, 128, 4, 1, 2, 1, 16, 64, 2, 128, 16, 2, 16, 128, 1, 4, 64, 8, 1, 8, 32, 4, 8, 16, 32, 1, 32, 16, 4, 128, 8, 4, 16, 1, 64, 1, 64, 128, 32, 128, 2, 32, 2, 8, 2, 4, 32, 64, 16, 8, 128, 64, 4, 2, 64, 32, 8, 64, 8};
    double resultArray[NELEMS(randomContention)] = {0};
    
    double sum = 0;
#pragma omp parallel 
{
	for(int i = 0 ; i < 10; i++)
	{
	#pragma omp barrier
	}	
}

#pragma omp parallel
    {
        int tid = omp_get_thread_num();
        int size = omp_get_num_threads();
        uint64_t myIters=0;
        uint64_t numIter = totalIters / numThreads;
        
        uint64_t myTicksStart = 0;
        uint64_t myTicksEnd = 0;
        uint64_t sensitivityTime = 0;
        struct drand48_data randSeedbuffer;
        srand48_r(tid, &randSeedbuffer);
        
#define POWER7_CLK_SPD (3860000000.0)
        
#define CLK_SPD POWER7_CLK_SPD
        
#define MILLI_SEC(n) (n * CLK_SPD/1000)
        
#define MICRO_SEC(n) (n * CLK_SPD/1000000)
        
#define SEC(n) (n * CLK_SPD)
        
        
        
#ifdef CHECK_THREAD_AFFINITY
        PrintAffinity(tid);
#endif
        LOCKNAME * hmcs = LockInit(tid, size, levels, participantsAtLevel);
        
        AllocateCS(tid, numThreads);
        // Warmup
        QNode me;
        const int warmupRounds = 20;
        RUN_LOOP(warmupRounds, 10, 0xffffffffffff);
        
        myTicksStart = 0;
        myTicksEnd = 0;
        sensitivityTime = 0;
        
        sensitivityTime = MILLI_SEC(HOW_LONG_MS);
        
        for(int round = 0; round < NITER; round ++) {
            
            hmcs->Reset();
            for(int i = 0 ; i < NELEMS(randomContention); i++) {
#pragma omp barrier
                double seconds =0;
                double myPerf = 0;
                
                // reset myIters
                myIters = 0;
                if(tid%randomContention[i])
                    goto L2;
                // Wait for sensitivityTime
                uint64_t myStart, myEnd;
                GET_TICK(myStart);
                RUN_LOOP(numIter, 1, sensitivityTime);
                GET_TICK(myEnd);
                seconds =  (myEnd - myStart) * 1.0 / SEC(1);
                myPerf = myIters  / seconds;
                
                if( (!(tid%randomContention[i])) && (round== (NITER-1)) ) {
#pragma omp atomic
                    sum +=  myIters;
                }
            L2:
#pragma omp barrier
                if(tid == 0 && round== (NITER-1)) {
                    resultArray[i] = sum ;
                    sum = 0;
                }
            }
            
        }
    }
    
    for(int i = 0 ; i < NELEMS(randomContention); i++){
        std::cout<<"\n" << resultArray[i];
    }
    
    
    elapsed = TIME_SPENT(startTime, endTime);
    double throughPut = (totalExecutedIters) * 1000000.0 / elapsed;
    std::cout<<"\n elapsed = " << elapsed;
    std::cout<<"\n totalExecutedIters = " << totalExecutedIters;
    std::cout<<"\n Throughput = " << throughPut << "\n";
    
#ifdef COMPUTE_LATENCY
    double averageThroughputLatency = 0;
    for(int i = 0 ; i < numThreads; i+=mustBeAMultile){
        averageThroughputLatency += throughPutLatency[i];
    }
    int workingThreads = numThreads / mustBeAMultile;
    averageThroughputLatency = averageThroughputLatency / workingThreads;
    std::cout<<"\n averageThroughputLatency = " << averageThroughputLatency << "\n";
#endif
    return 0;
}

