#define _GNU_SOURCE 1

#include <asm/unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <linux/perf_event.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>
#include<omp.h>
#include <errno.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <fcntl.h>
#include <sched.h>

#define handle_error_en(en, msg) \
do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

#define NUM_CPUS (8)


long perf_event_open(struct perf_event_attr* event_attr, pid_t pid, int cpu, int group_fd, unsigned long flags) {
    return syscall(__NR_perf_event_open, event_attr, pid, cpu, group_fd, flags);
}

static void perf_event_handler(int signum, siginfo_t* info, void* ucontext) {
    pthread_t         self;
    self = pthread_self();
    switch(info->si_code){
        case POLL_IN: printf("\n POLL_IN  %d--OMP:%d on %d FD=%d\n", self, omp_get_thread_num(), sched_getcpu(), info->si_fd); break;
        case POLL_HUP: printf("\n POLL_HUP  %d--OMP:%d on %d FD=%d\n", self, omp_get_thread_num(), sched_getcpu(), info->si_fd); break;
        default: printf("\n BAD! %d  %d--OMP:%d on %d FD=%d", info->si_code, self, omp_get_thread_num(), sched_getcpu(), info->si_fd); break;
    }
    ioctl(info->si_fd, PERF_EVENT_IOC_REFRESH, 1);
}


// Set thread to run on all CPUs
void SetAffinityAll(){
    int s, j;
    cpu_set_t cpuset;
    pthread_t thread;
    thread = pthread_self();
    CPU_ZERO(&cpuset);
    for(int where =0 ; where < NUM_CPUS ; where++)
        CPU_SET(where, &cpuset);
    s = pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_setaffinity_np");
}


// Set thread to run on given CPU
void SetAffinity(int where){
    int s, j;
    cpu_set_t cpuset;
    pthread_t thread;
    thread = pthread_self();
    CPU_ZERO(&cpuset);
    CPU_SET(where, &cpuset);
    s = pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_setaffinity_np");
}

int worker() {
    // Configure signal handler
    struct sigaction sa;
    memset(&sa, 0, sizeof(struct sigaction));
    sa.sa_sigaction = perf_event_handler;
    sa.sa_flags = SA_SIGINFO;
    
    // Setup signal handler
    if (sigaction(SIGIO, &sa, NULL) < 0) {
        fprintf(stderr,"Error setting up signal handler\n");
        perror("sigaction");
        exit(EXIT_FAILURE);
    }
    
    // Configure perf_event_attr struct
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(struct perf_event_attr));
    pe.type = PERF_TYPE_SOFTWARE; // S/w event
    pe.size = sizeof(struct perf_event_attr);
    pe.config = PERF_COUNT_SW_CPU_MIGRATIONS;     // Count page faults
    //pe.config = PERF_COUNT_SW_CONTEXT_SWITCHES;     // Count ctxt switches
    //pe.config = PERF_COUNT_SW_PAGE_FAULTS_MIN;     // Count migrations
    pe.disabled = 1;        // Event is initially disabled
    pe.sample_type = PERF_SAMPLE_IP;
    pe.sample_period = 1; // Triggers signals on each sample
    ///pe.wakeup_events = 1; // No idea how to use this
    pe.exclude_kernel = 0;      // include events that happen in the kernel-space
    pe.exclude_hv = 1;          // excluding events that happen in the hypervisor
    
    pid_t pid = syscall(SYS_gettid);  // measure the current process/thread
    int cpu = -1;   // measure on any cpu
    int group_fd = -1;
    unsigned long flags = 0;
    
    int fd = perf_event_open(&pe, pid, cpu, group_fd, flags);
    if (fd == -1) {
        fprintf(stderr, "Error opening leader %llx\n", pe.config);
        perror("perf_event_open");
        exit(EXIT_FAILURE);
    }
    
    // Setup event handler for overflow signals
    fcntl(fd, F_SETFL, O_NONBLOCK|O_ASYNC);
    fcntl(fd, F_SETSIG, SIGIO);
    struct f_owner_ex ex;
    ex.type = F_OWNER_TID;
    ex.pid = syscall(SYS_gettid);
    fcntl(fd, F_SETOWN_EX, &ex); // Ensures signal is delivered to THIS thread.
    
    long loopCount = 10000000;
    long i = 0;
    int me = omp_get_thread_num();
    unsigned curCpu=0;
    unsigned oldCpu=me% NUM_CPUS;
    
    // SetAffinity(me % NUM_CPUS);
    //SetAffinity();
    
    // Put thread 1 on all CPUs and bind the rest to only one CPU
    if(omp_get_thread_num() == 1)
        SetAffinityAll();
    else
        SetAffinity(me % NUM_CPUS);
    
    
    // Start monitoring
    ioctl(fd, PERF_EVENT_IOC_RESET, 0);     // Reset event counter to 0
    ioctl(fd, PERF_EVENT_IOC_REFRESH, 0xefffff);   //max signals delivered
    ioctl(fd, PERF_EVENT_IOC_ENABLE, 0);   //enable
    
    
    // Spend some time...
    if(omp_get_thread_num() == 1)
    {
        
        for(i = 0; i < loopCount; i++) {
            if(i %10 == 0)
            {
                //char * i = calloc(4096, 1);
                //SetAffinity(me++ % NUM_CPUS );
                //SetAffinity(me % NUM_CPUS );
                write(1,".", 1);
                sleep(.1);
            }
            
            // Log any thread migration
            curCpu = sched_getcpu();
            if(oldCpu != curCpu) {
                printf("\n OMP:%d -> Migrated from %d to %d\n",omp_get_thread_num(), oldCpu, curCpu);
                oldCpu = curCpu;
            }
        }
        
    }

#pragma omp barrier
    ioctl(fd, PERF_EVENT_IOC_DISABLE, 0);   // Disable event
    
    long long counter;
    read(fd, &counter, sizeof(long long));  // Read event counter value
    
    printf("OMP:%d  Counter value %lld\n", omp_get_thread_num(), counter);
    
    close(fd);
}

int main(){
#pragma omp parallel
    {
        worker();
    }
    return 0;
}

