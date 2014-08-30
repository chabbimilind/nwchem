#ifndef __UTIL_H__
#define __UTIL_H_

#include <sched.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <omp.h>
#include <assert.h>
#include <sys/time.h>
#include <iostream>
#include <malloc.h>
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <unistd.h>
#include <sys/syscall.h>    /* For SYS_xxx definitions */

#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (0xffffffffffffffff)
#define ACQUIRE_PARENT (0xfffffffffffffffe)
#define COHORT_START (0x1)
#define ALARM_TIME (3 * 60)

#if defined(__xlC__) || defined (__xlc__)
#include<builtins.h>
static inline int64_t PPCSwap(volatile int64_t * addr, int64_t value) {
 	for(;;){
		const int64_t oldVal = __ldarx(addr);
		if(__stdcx(addr, value)) {
			return oldVal;
		}
	}
}

static inline bool PPCBoolCompareAndSwap(volatile int64_t * addr, int64_t oldValue, int64_t newValue) {
    for(;;) {
        const int64_t val = __ldarx(addr);
        if (val != oldValue) {
            return false;
        }
        if(__stdcx(addr, newValue)) {
            return true;
        }
    }
}
#define CAS(location, oldValue, newValue) assert(0 && "NYI")
#define SWAP(location, value) PPCSwap((volatile int64_t *)location, (int64_t)value)
#define BOOL_CAS(location, oldValue, newValue) PPCBoolCompareAndSwap((volatile int64_t *)location, (int64_t)oldValue, (int64_t)newValue)
#define ATOMIC_ADD(location, value) __fetch_and_andlp((volatile int64_t *) location, value)
#define FORCE_INS_ORDERING() __isync()
#define COMMIT_ALL_WRITES() __lwsync()
#else
// ASSUME __GNUC__
#define CAS(location, oldValue, newValue) __sync_val_compare_and_swap(location, oldValue, newValue)
#define SWAP(location, value) __sync_lock_test_and_set(location, value)
#define BOOL_CAS(location, oldValue, newValue) __sync_bool_compare_and_swap(location, oldValue, newValue)
#define ATOMIC_ADD(location, value) __sync_fetch_and_add(location,value)

#ifdef __PPC__
#define FORCE_INS_ORDERING() __asm__ __volatile__ (" isync\n\t")
#define COMMIT_ALL_WRITES() __asm__ __volatile__ (" lwsync\n\t")
#elif defined(__x86_64__)
#define FORCE_INS_ORDERING() do{}while(0)
#define COMMIT_ALL_WRITES() do{}while(0)
#else
assert( 0 && "unsupported platform");
#endif

#endif
#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

#define CACHE_LINE_SIZE (128)

//#define DOWORK
//#define VALIDATE
/* for performance measurement on small number of levels, disable try release */
/* for correctness checks enable try release */
//#define TRY_RELEASE
#define CHECK_THREAD_AFFINITY

#ifdef VALIDATE
volatile int var = 0;
#endif

#ifdef DOWORK
struct InsideCS{
    volatile uint64_t f1 __attribute__((aligned(CACHE_LINE_SIZE)));
    volatile uint64_t f2 __attribute__((aligned(CACHE_LINE_SIZE)));
}__attribute__((aligned(CACHE_LINE_SIZE)));


InsideCS gInsideCS;

// Touch 2 shared variables when inside a critical section
void DoWorkInsideCS(){
    gInsideCS.f1++;
    gInsideCS.f2++;
}

// perform some dummy operations and spend time when outside critical section
void DoWorkOutsideCS(){
    volatile uint64_t i = 0;
    volatile uint64_t end = 4 * 1000;
    volatile uint64_t inc = 1;
    for (; i < end; i += inc)
        ;
}
#endif


#define handle_error_en(en, msg) \
do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

/* taken from https://computing.llnl.gov/tutorials/pthreads/man/pthread_setaffinity_np.txt */
void PrintAffinity(int tid){
#define NUM_CPUS (10000)
    int s, j;
    cpu_set_t  cpuset;// = CPU_ALLOC(NUM_CPUS);
/*    if (cpusetp == NULL) {
               perror("CPU_ALLOC");
               exit(EXIT_FAILURE);
    }
    size_t size = CPU_ALLOC_SIZE(NUM_CPUS);
*/
    size_t size = sizeof(cpu_set_t);//CPU_ALLOC_SIZE(NUM_CPUS);
    CPU_ZERO(&cpuset);


    pthread_t thread;
    
    thread = pthread_self();
    
    /* Set affinity mask to include CPUs tid */
    
    CPU_ZERO(&cpuset);
    CPU_SET(1*tid,&cpuset);
    if(tid == 0 )
        printf("CPU_SET(1*tid, &cpuset);\n");
    
#if 1
    s = pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_setaffinity_np");
#endif

#if 0
    /* Check the actual affinity mask assigned to the thread */
    
    s = pthread_getaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_getaffinity_np");
    
    //printf("Set returned by pthread_getaffinity_np() contained:\n");
    assert(CPU_COUNT_S(size, cpusetp) == 1);
#pragma omp ordered
{
    for (j = 0; j < CPU_SETSIZE; j++)
        if (CPU_ISSET(j, &cpuset))
            printf("    %d: CPU %d\n", tid,j);
}
#endif
#undef NUM_CPUS
}

#endif

