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


#define  LOCKED (false)
#define  UNLOCKED (true)

#define WAIT (0xffffffffffffffff)
#define ACQUIRE_PARENT (0xfffffffffffffffe)
#define COHORT_START (0x1)

#define CAS(a, b, c) __sync_val_compare_and_swap(a, b, c)
#define SWAP(a,b) __sync_lock_test_and_set(a, b)
#define BOOL_CAS(a, b, c) __sync_bool_compare_and_swap(a, b, c)

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

#define CACHE_LINE_SIZE (128)

#define DOWORK
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

#endif
