#ifndef __UTIL_H__
#define __UTIL_H_


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


#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (0xffffffffffffffff)
#define ACQUIRE_PARENT (0xfffffffffffffffe)
#define COHORT_START (0x1)


#if defined(__xlC__) || defined (__xlc__)
#include<builtins.h>
/* copied from http://www.ibm.com/developerworks/aix/library/au-inline_assembly/index.html?ca=dat */
        void inline compare_and_swap (volatile int * p, int oldval, int newval) {
        int fail;
        __asm__ __volatile__ (
           "0: lwarx %0, 0, %1\n\t"
                 "      xor. %0, %3, %0\n\t"
              " bne 1f\n\t"
            " stwcx. %2, 0, %1\n\t"
                 "      bne- 0b\n\t"
            " isync\n\t"
        "1: "
        : "=&r"(fail)
        : "r"(p), "r"(newval), "r"(oldval)
        : "cr0");
        }

static inline int64_t PPCSwap(volatile int64_t * addr, int64_t value) {
	for(;;){ 
		int64_t oldVal = __ldarx(addr);
		if(__stdcx(addr, value))
			return oldVal;
	}
}

static inline bool PPCBoolCompareAndSwap(volatile int64_t * addr, int64_t oldValue, int64_t newValue) {
	int64_t val = __ldarx(addr);
	if (val != oldValue)
		return false;
	if(__stdcx(addr, newValue))
		return true;
	return false;
}


#define CAS(location, oldValue, newValue) assert(0 && "NYI")
#define SWAP(location, value) PPCSwap((volatile int64_t *)location, (int64_t)value)
#define BOOL_CAS(location, oldValue, newValue) PPCBoolCompareAndSwap((volatile int64_t *)location, (int64_t)oldValue, (int64_t)newValue)
#define FORCE_INS_ORDERING() __isync()
#define COMMIT_ALL_WRITES() __lwsync()
#else
// ASSUME __GNUC__
#define CAS(location, oldValue, newValue) __sync_val_compare_and_swap(location, oldValue, newValue)
#define SWAP(location, value) __sync_lock_test_and_set(location, value)
#define BOOL_CAS(location, oldValue, newValue) __sync_bool_compare_and_swap(location, oldValue, newValue)
#define FORCE_INS_ORDERING() do{}while(0)
#define COMMIT_ALL_WRITES() do{}while(0)
#endif

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

#define CACHE_LINE_SIZE (128)

//#define DOWORK
//#define VALIDATE


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
    int s, j;
    cpu_set_t cpuset;
    pthread_t thread;
    
    thread = pthread_self();
    
    /* Set affinity mask to include CPUs 0 to 7
    
    CPU_ZERO(&cpuset);
    for (j = 0; j < 8; j++)
        CPU_SET(j, &cpuset);
    
    s = pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_setaffinity_np");
   */
    /* Check the actual affinity mask assigned to the thread */
    
    s = pthread_getaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_getaffinity_np");
    
    printf("Set returned by pthread_getaffinity_np() contained:\n");
    for (j = 0; j < CPU_SETSIZE; j++)
        if (CPU_ISSET(j, &cpuset))
            printf("    %d: CPU %d\n", tid,j);
}

#endif
