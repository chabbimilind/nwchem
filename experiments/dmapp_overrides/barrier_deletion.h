#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <sys/stat.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <limits.h>
#include <sys/time.h>
#include <sys/resource.h>
#include<dmapp.h>

extern "C" {
    extern __thread uint8_t gSharedDataAccessStatus;
    extern __thread bool gRemoteGetSeen;
    extern void enable_barrier_optimization_();
    extern void disable_barrier_optimization_();
    extern void disable_and_cleanup_barrier_optimization_();
    extern void UnprotectAllPages();
    
#define SHARED_DATA_ACCESSED_REMOTE (1 << 0)
#define SHARED_DATA_ACCESSED_LOCAL  (1 << 1)
#define SET_SHARED_DATA_ACCESS_STATE(state) do {( gSharedDataAccessStatus |= (state)); } while(0)
#define CLEAR_SHARED_DATA_ACCESS_STATE(state) do {( gSharedDataAccessStatus &= ~(state)); } while(0)
}
