#include<mpi.h>
#include<dmapp.h>
#include<iostream>
#include<stdlib.h>
#include<string.h>
#include<assert.h>
#include<stdint.h>
#include<stdlib.h>
#include<sys/time.h>

using namespace std;


#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)


dmapp_lock_desc_t   * lock_addr;
dmapp_seg_desc_t    * lock_seg;

uint64_t DoExperiment(int numIter) {
	struct timeval start;
	struct timeval end;
	uint64_t span;
	dmapp_lock_desc_t lock_addr;
	bzero(&lock_addr, sizeof(lock_addr));
	int lock_host = 0;
	uint64_t flags = 0;
	dmapp_lock_handle_t handle;



	gettimeofday(&start, 0);
	for(int i = 0; i < numIter; i++){
		dmapp_return_t ret = dmapp_lock_acquire(&lock_addr, &lock_seg, lock_host, flags, &handle);
		assert(DMAPP_RC_SUCCESS == ret);
		ret = dmapp_lock_release(handle, flags);
		assert(DMAPP_RC_SUCCESS == ret);
	}
	gettimeofday(&end, 0);
	return  TIME_SPENT(start, end);

}

#define ALLOC_SIZE (1024)

void PrepareLock(int me, int size){
	lock_addr = (dmapp_lock_desc_t*) malloc(size * sizeof(dmapp_lock_desc_t));
	lock_seg = (dmapp_seg_desc_t*) malloc(size * sizeof(dmapp_seg_desc_t));
        // allocate and register mem
	int rc = posix_memalign((void**) (&lock_desc[me]), 4096, sizeof(dmapp_lock_desc_t));
	assert(0 == rc);

	dmapp_return_t status = dmapp_mem_register(&lock_desc[me], sizeof(dmapp_lock_desc_t), &lock_seg[me]);
	assert(status == DMAPP_RC_SUCCESS);

	// Share the region with all processes:
        MPI_Allgather(&lock_seg, sizeof(dmapp_seg_desc_t), MPI_BYTE, 0 ,  MPI_COMM_WORLD);
        MPI_Allgather(sharedData, sizeof(dmapp_lock_desc_t), MPI_BYTE, 0 ,  MPI_COMM_WORLD);

}

int main(int argc, char ** argv){
	MPI_Init(&argc, &argv);		
	int rank, size;
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);	/* get current process id */
	MPI_Comm_size(MPI_COMM_WORLD, &size);	/* get number of processes */


	dmapp_rma_attrs_t actual_args;
	dmapp_init(NULL, &actual_args);


	int numIter =  (1<<20); //atoi(argv[1]);
	// allocate and register mem
	if(rank == 0) {
		int rc = posix_memalign((void**) (&sharedData), 4096, ALLOC_SIZE);
		assert(0 == rc);
    		assert(sharedData);

    		dmapp_return_t status = dmapp_mem_register(sharedData, ALLOC_SIZE, &lock_seg);
    		assert(status == DMAPP_RC_SUCCESS);
	}

	// Share the region with all processes:
        MPI_Bcast(&lock_seg, sizeof(dmapp_seg_desc_t), MPI_BYTE, 0 ,  MPI_COMM_WORLD);
        MPI_Bcast(sharedData, sizeof(dmapp_lock_desc_t), MPI_BYTE, 0 ,  MPI_COMM_WORLD);
	

	// warmup
	DoExperiment(10);



	if(rank == 0)
		cout<<endl<<"nproc"<<"\t"<<"Time";


	DoExperiment(numIter);

	if(rank == 0)
		dmapp_mem_unregister(&lock_seg);

	dmapp_finalize();
	MPI_Finalize();
	return 0;

}

