#include<mpi.h>
#include<iostream>
#include<stdlib.h>
#include<string.h>
#include<assert.h>
#include<stdint.h>
#include<sys/time.h>

using namespace std;


#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)


int main(int argc, char ** argv){

	MPI_Init(&argc, &argv);		
	int rank, size;
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);	/* get current process id */
	MPI_Comm_size(MPI_COMM_WORLD, &size);	/* get number of processes */
	
	int numIter =  (1<<20); //atoi(argv[1]);
	// Warmup
	MPI_Barrier(MPI_COMM_WORLD);


        struct timeval start;
        struct timeval end;
        uint64_t barrierTime;
        uint64_t allreduceTime;


        gettimeofday(&start, 0);
        // Phase 1: receiver calls MPI_Irecv(..., 0 /* sender */, ...)
        for(int i = 0; i < numIter; i++){
		MPI_Barrier(MPI_COMM_WORLD);
        }
        gettimeofday(&end, 0);
        barrierTime= TIME_SPENT(start, end);


	if(rank == 0)
		cout<<endl<<"barrierTime:"<<barrierTime;


	// Warmup
	int sendBuf = 10, recvBuf = 10;
	MPI_Allreduce(&sendBuf, &recvBuf, 1, MPI_INT,MPI_MIN,MPI_COMM_WORLD);
        gettimeofday(&start, 0);
        // Phase 1: receiver calls MPI_Irecv(..., 0 /* sender */, ...)
        for(int i = 0; i < numIter; i++){
		MPI_Allreduce(&sendBuf, &recvBuf, 1, MPI_INT,MPI_MIN,MPI_COMM_WORLD);
        }
        gettimeofday(&end, 0);
        allreduceTime= TIME_SPENT(start, end);

	if(rank == 0)
		cout<<endl<<"allreduceTime:"<<allreduceTime;

	MPI_Finalize();
	return 0;

}

