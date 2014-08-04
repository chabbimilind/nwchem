#include <mpi.h>
#include <dmapp.h>
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/time.h>
#include <errno.h>
#include <malloc.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

#define handle_error(msg) \
do { perror(msg); exit(EXIT_FAILURE); } while (0)

using namespace std;


#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

void   ** sharedPointers;
dmapp_seg_desc_t     * sharedSegments;
void * mySharedPtr;

void *tmpData = NULL;
int myRank;
int  mpiCommSize;

#define ALLOC_SIZE ((1<<20))

void SegvHandler (int num)  {
	//printf ("memory accessed!\n");
	mprotect (mySharedPtr, ALLOC_SIZE, PROT_READ | PROT_WRITE);
}

uint64_t DoExperiment() {
    
    // Circulate data
	for(int i = 1; i < mpiCommSize; i++){
        
        // Process me reads from process me + 1 in round 1.
        // Process me writes to process me - 1
        
        // In round i it will get data from process (myRank + 2*i-1)
        
        int to = myRank == 0 ? mpiCommSize -1 : (myRank - 1) ;
        int from = (myRank + 1) % mpiCommSize;
        
        //printf("\n Me = %d, from = %d, to = %d", myRank, from, to);
        
        dmapp_return_t ret = dmapp_get_nbi(
                                           /*target_addr*/ tmpData,
                                           /*source_addr */ sharedPointers[from],
                                           /*source_seg*/ &sharedSegments[from],
                                           /*source_pe*/ from,
                                           /*nelems */ ALLOC_SIZE,
                                           DMAPP_BYTE);
        assert(DMAPP_RC_SUCCESS == ret);
        ret = dmapp_gsync_wait();
        assert(DMAPP_RC_SUCCESS == ret);
        
        
        // check that the data is correct
        for(int x = 0 ; x < ALLOC_SIZE; x++){
            int val = ((uint8_t*)tmpData)[i];
            if(myRank == 0 && (val != (myRank + 2*i-1) % mpiCommSize)) {
                printf("\n Me = %d, from = %d, to = %d, expected = %d, found = %d\n", myRank, from, to, (myRank + 2*i-1) % mpiCommSize, val);
            }
            assert( val == (myRank + 2*i-1) % mpiCommSize);
        }
        
        
        MPI_Barrier(MPI_COMM_WORLD);
        
        // Process i writes to process i - 1
        
        ret = dmapp_put_nbi(
                            /*target_addr*/ sharedPointers[to],
                            /*target_seg*/ &sharedSegments[to],
                            /*target_pe*/ to,
                            /* source_addr */ tmpData,
                            /*nelems */ ALLOC_SIZE,
                            DMAPP_BYTE);
        assert(DMAPP_RC_SUCCESS == ret);
        ret = dmapp_gsync_wait();
        assert(DMAPP_RC_SUCCESS == ret);
        
        MPI_Barrier(MPI_COMM_WORLD);
    }
}

int main(int argc, char ** argv){
	MPI_Init(&argc, &argv);
	MPI_Comm_rank(MPI_COMM_WORLD, &myRank);	/* get current process id */
	MPI_Comm_size(MPI_COMM_WORLD, &mpiCommSize);	/* get number of processes */
    
    
    assert(mpiCommSize <= (256) && "Test written only for a max of 256 myRanks");
    
	dmapp_rma_attrs_t actual_args;
	dmapp_init(NULL, &actual_args);
    
	// signal handler
	struct sigaction sa;
    
	/* Install SegvHandler as the handler for SIGSEGV. */
	memset (&sa, 0, sizeof (sa));
	sa.sa_handler = &SegvHandler;
	sigaction (SIGSEGV, &sa, NULL);
    
	// allocate and register mem
    sharedSegments = (dmapp_seg_desc_t *) calloc(sizeof(dmapp_seg_desc_t), mpiCommSize);
    sharedPointers = (void **) calloc(sizeof(void*), mpiCommSize);
    
    dmapp_seg_desc_t my_sharedSegments;
    int rc = posix_memalign((void**) (&mySharedPtr), getpagesize(), ALLOC_SIZE);
    assert(0 == rc);
    assert(mySharedPtr);
    // Init mySharedPtr with myRank
    memset(mySharedPtr, myRank, ALLOC_SIZE);
    
    dmapp_return_t status = dmapp_mem_register(mySharedPtr, ALLOC_SIZE, &my_sharedSegments);
    assert(status == DMAPP_RC_SUCCESS);
    
    
    // Init tmpData with 0
    rc = posix_memalign((void**) (&tmpData), getpagesize(), ALLOC_SIZE);
    assert(0 == rc);
	memset(tmpData, 0, ALLOC_SIZE);
    
    
	// Share the region with all processes:
	MPI_Allgather(&my_sharedSegments, sizeof(dmapp_seg_desc_t), MPI_BYTE, sharedSegments , sizeof(dmapp_seg_desc_t), MPI_BYTE, MPI_COMM_WORLD);
	MPI_Allgather(&mySharedPtr, sizeof(void   *), MPI_BYTE, sharedPointers , sizeof(void   *), MPI_BYTE, MPI_COMM_WORLD);
    
    
    for(int k = 0 ; k < mpiCommSize; k++) {
        if(myRank == 0){
            printf("\n %p .. %p, %d, %d",sharedPointers[k], &sharedSegments[myRank], sharedSegments[myRank].addr, sharedSegments[myRank].len);
        }
    }
    
    
    MPI_Barrier(MPI_COMM_WORLD);
    
    sharedSegments[myRank] = my_sharedSegments;
    sharedPointers[myRank] = mySharedPtr;
    
    // Run the experiment 100 times
    for(int i = 0; i < 100; i++) {
        if(myRank == 0) {
            printf(".");
            fflush(stdout);
        }
        // init mySharedPtr
        memset(mySharedPtr, myRank, ALLOC_SIZE);
        // mprotect mySharedPtr
        rc = mprotect(mySharedPtr, ALLOC_SIZE, PROT_NONE);
        assert(0 == rc);
        MPI_Barrier(MPI_COMM_WORLD);
        DoExperiment();
    }
    
    
    MPI_Barrier(MPI_COMM_WORLD);
    
    dmapp_mem_unregister(&sharedSegments[myRank]);
    if(myRank == 0)
        printf(" Done\n");
    
	dmapp_finalize();
	MPI_Finalize();
    
    
	return 0;
    
}

