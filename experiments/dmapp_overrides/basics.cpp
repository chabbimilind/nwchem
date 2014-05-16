
#include <stdio.h>
#include <execinfo.h>
#include <stdlib.h>
#include <tr1/unordered_map>
#include <stdint.h>
#include <sys/stat.h>
#include <iostream>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <sstream>
#include <limits.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sstream>
#include<dmapp.h>
#include<mpi.h>


#define ALL_REDUCE_BUFFER(status) ( ((status) << 32 ) | barrierInstance)
#define ALL_REDUCE_GET_STATUS(buffer) ( (buffer) >> 32 )
#define ALL_REDUCE_GET_INSTANCE(buffer) ((buffer) & 0xffffffff)


uint64_t barrierInstance  = 2;
static void MyUserFn(void* a, void* b, int* len, MPI_Datatype* type) {
    uint64_t a1 = *((uint64_t*)a);
    uint64_t b1 = *((uint64_t*)b);
    uint32_t statusA = ALL_REDUCE_GET_STATUS(a1);
    uint32_t statusB = ALL_REDUCE_GET_STATUS(b1);
    uint32_t instanceA = ALL_REDUCE_GET_INSTANCE(a1);
    uint32_t instanceB = ALL_REDUCE_GET_INSTANCE(b1);
    uint64_t retStatus = statusA < statusB ? statusA : statusB;
    uint64_t retInstance = instanceA < instanceB ? instanceA : instanceB;
    *((uint64_t*)b) = (((retStatus) << 32) | retInstance);
}

int main() {
    uint64_t a = 1;
    barrierInstance = 2;
    uint64_t buf = ALL_REDUCE_BUFFER(a);
    printf("\n a =1 , b=2, buf = %lx", buf);
    printf("\n buf = %lx, a =%x , b=%x", buf, ALL_REDUCE_GET_STATUS(buf), ALL_REDUCE_GET_INSTANCE(buf));
    return 0;
}
