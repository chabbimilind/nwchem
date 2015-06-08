#ifndef __UTIL_H__
#define __UTIL_H__


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
#include <unistd.h>
#include <signal.h>
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
            //__isync();
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
#define ATOMIC_ADD(location, value) __fetch_and_addlp((volatile int64_t *) location, (int64_t) value)
#define FORCE_INS_ORDERING() __isync()
#define COMMIT_ALL_WRITES() __lwsync()
#define GET_TICK(var) __asm__ __volatile__ ("mfspr %0, 268\n\t": "=r" (var): )
#else
// ASSUME __GNUC__
#define CAS(location, oldValue, newValue) __sync_val_compare_and_swap(location, oldValue, newValue)
#define SWAP(location, value) __sync_lock_test_and_set(location, value)
#define BOOL_CAS(location, oldValue, newValue) __sync_bool_compare_and_swap(location, oldValue, newValue)
#define ATOMIC_ADD(location, value) __sync_fetch_and_add((volatile int64_t *) location, (int64_t) value)

#ifdef __PPC__
#define FORCE_INS_ORDERING() __asm__ __volatile__ (" isync\n\t")
#define COMMIT_ALL_WRITES() __asm__ __volatile__ (" lwsync\n\t")
#define GET_TICK(var) __asm__ __volatile__ ("mfspr %0, 268\n\t": "=r" (var): )

#elif defined(__x86_64__)
#define FORCE_INS_ORDERING() do{}while(0)
#define COMMIT_ALL_WRITES() do{}while(0)
#define GET_TICK(var) assert(0 && "NYI")
#else
assert( 0 && "unsupported platform");
#endif

#endif

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

#ifndef CACHE_LINE_SIZE
#define CACHE_LINE_SIZE (128)
#endif

//#define DOWORK
//#define VALIDATE
#define CHECK_THREAD_AFFINITY

#ifdef VALIDATE
volatile int var = 0;
#endif

#ifdef DOWORK
/*
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
*/

struct CriticalData_t{
    uint64_t data __attribute__((aligned(CACHE_LINE_SIZE)));
    inline void* operator new(size_t size) {
        void *storage = memalign(CACHE_LINE_SIZE, size);
        if(NULL == storage) {
            throw "allocation fail : no free memory";
        }
        return storage;
    }
} __attribute__((aligned(CACHE_LINE_SIZE)));

// +1 to allow for MAX_DATA = 0
CriticalData_t * gCriticalData[MAX_DATA + 1] __attribute__((aligned(CACHE_LINE_SIZE)));

// Touch shared variables when inside a critical section
void DoWorkInsideCS(){
    for(int i = 0 ; i < MAX_DATA; i++)
        gCriticalData[i]->data++;
}

// Each thread allocates its share of data
void static AllocateCS(int tid, int numThreads){
    for(int i = tid ; i < MAX_DATA; i+=numThreads) {
        gCriticalData[i] = new CriticalData_t();
        gCriticalData[i]->data = 0; // first touch
    }
#pragma omp barrier
#pragma omp single 
    {
        
        // jumble
        srand(0);
        for(int i = 0; i < MAX_DATA; i++) {
            int randIndex = rand() % MAX_DATA;
            // swap
            CriticalData_t * tmp =  gCriticalData[randIndex];
            gCriticalData[randIndex] = gCriticalData[i];
            gCriticalData[i] = tmp;
        }
    }
}


// perform some dummy operations and spend time when outside critical section
void DoWorkOutsideCS(struct drand48_data * randSeedbuffer){
#define MAX_SLEEP (1000)
#define MIN_SLEEP (3000)
        double randNum;
        //drand48_r(randSeedbuffer, &randNum);
        uint64_t maxWait = THE_WAIT;//MIN_SLEEP + MAX_SLEEP * randNum;
        volatile int i = 0;
        while(i++ < maxWait);
}
/*
void DoWorkOutsideCS(){
    volatile uint64_t i = 0;
    volatile uint64_t end = 4 * 1000;
    volatile uint64_t inc = 1;
    for (; i < end; i += inc)
        ;
}
*/
#endif


#define handle_error_en(en, msg) \
do { errno = en; perror(msg); exit(EXIT_FAILURE); } while (0)

/* taken from https://computing.llnl.gov/tutorials/pthreads/man/pthread_setaffinity_np.txt */
void PrintAffinity(int tid){
#ifdef BLACKLIGHT
    return;
#endif
    int s, j;
    cpu_set_t cpuset;
    pthread_t thread;
    
    thread = pthread_self();
    
    /* Set affinity mask to include CPUs tid */
    
    CPU_ZERO(&cpuset);
    CPU_SET(1*tid, &cpuset);
    if(tid == 0 )
        printf("CPU_SET(1*tid, &cpuset);\n");
    
    s = pthread_setaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_setaffinity_np");
#if 0
    /* Check the actual affinity mask assigned to the thread */
    
    s = pthread_getaffinity_np(thread, sizeof(cpu_set_t), &cpuset);
    if (s != 0)
        handle_error_en(s, "pthread_getaffinity_np");
    
    printf("Set returned by pthread_getaffinity_np() contained:\n");
    for (j = 0; j < CPU_SETSIZE; j++)
        if (CPU_ISSET(j, &cpuset))
            printf("    %d: CPU %d\n", tid,j);
#endif
}

#endif

