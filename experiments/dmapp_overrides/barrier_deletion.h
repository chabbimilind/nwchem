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
    extern __thread bool gAccessedRemoteData;
    extern void enable_barrier_optimization_();
    extern void disable_barrier_optimization_();
    extern void disable_and_cleanup_barrier_optimization_();
}
