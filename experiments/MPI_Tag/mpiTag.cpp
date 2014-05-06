#include<mpi.h>
#include<iostream>
#include<stdlib.h>
#include<string.h>
#include<assert.h>
#include<stdint.h>
#include<sys/time.h>

using namespace std;

//#define batchSize (2)
#define MAX_BATCH_SIZE (64)

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

uint64_t uniqueTag;

char **msg;

void DoSendExperiment(int msgSize, int batchSize, int numIter) {
	
	MPI_Request request[batchSize];
	MPI_Status status[batchSize];

	struct timeval start;
	struct timeval end;
	uint64_t designatedReceiverTime;
	uint64_t anyReceiverTime;


	gettimeofday(&start, 0);
	// Phase 1: receiver calls MPI_Irecv(..., 0 /* sender */, ...)
	for(int i = 0; i < numIter; i++){
		for(int j = 0; j < batchSize; j++){
			MPI_Isend(msg[j], msgSize, MPI_CHAR, 1 /*destination */, uniqueTag++ /*tag*/, MPI_COMM_WORLD, & request[j]);
			//MPI_Send(msg[j], msgSize, MPI_CHAR, 1 /*destination */, uniqueTag++ /*tag*/, MPI_COMM_WORLD);
		}	
		MPI_Waitall(batchSize, request, status);
	}
	gettimeofday(&end, 0);
	designatedReceiverTime = TIME_SPENT(start, end);

	gettimeofday(&start, 0);
	// Phase 2: receiver calls MPI_Irecv(...,  /* sender */, ...)
        for(int i = 0; i < numIter; i++){
                for(int j = 0; j < batchSize; j++){
                        MPI_Isend(msg[j], msgSize, MPI_CHAR, 1 /*destination */, uniqueTag++ /*tag*/, MPI_COMM_WORLD, & request[j]);
                        //MPI_Send(msg[j], msgSize, MPI_CHAR, 1 /*destination */, uniqueTag++ /*tag*/, MPI_COMM_WORLD);
                }
                MPI_Waitall(batchSize, request, status);
        }
	gettimeofday(&end, 0);
	anyReceiverTime = TIME_SPENT(start, end);

	cout<<endl<<batchSize<<"\t"<<msgSize<<"\t"<<designatedReceiverTime<<"\t"<<anyReceiverTime;

}

void DoRecvExperiment(int msgSize, int batchSize, int numIter) {
	
	MPI_Request request[batchSize];
	MPI_Status status[batchSize];

	int sender = 0;


	// Phase 1: receiver calls MPI_Irecv(..., 0 /* sender */, ...)
	for(int i = 0; i < numIter; i++){
		for(int j = 0; j < batchSize; j++){
			MPI_Irecv(msg[j], msgSize, MPI_CHAR, sender, MPI_ANY_TAG, MPI_COMM_WORLD, & request[j]);
			//MPI_Recv(msg[j], msgSize, MPI_CHAR, sender, MPI_ANY_TAG, MPI_COMM_WORLD, &status[0]);
		}	
		MPI_Waitall(batchSize, request, status);
	}



	sender = MPI_ANY_SOURCE;
	// Phase 2: receiver calls MPI_Irecv(..., MPI_SOURCE_ANY /* sender */, ...)
	for(int i = 0; i < numIter; i++){
		for(int j = 0; j < batchSize; j++){
			MPI_Irecv(msg[j], msgSize, MPI_CHAR, sender, MPI_ANY_TAG, MPI_COMM_WORLD, & request[j]);
			//MPI_Recv(msg[j], msgSize, MPI_CHAR, sender, MPI_ANY_TAG, MPI_COMM_WORLD, &status[0]);
		}	
		MPI_Waitall(batchSize, request, status);
	}

}

void AllocateMsgBuffer(int msgSize){
	for(int i = 0 ; i < MAX_BATCH_SIZE; i++)
		msg[i] = (char*)malloc(msgSize);
}

void FreeMsgBuffer(){
	for(int i = 0 ; i < MAX_BATCH_SIZE; i++)
		free(msg[i]);
}

int main(int argc, char ** argv){
/*
	if(argc != 2) {
		cout<< "Usage:" <<argv[0] << "<num iter>\n";
		exit(-1);
	}
*/

	MPI_Init(&argc, &argv);		
	int rank, size;
	MPI_Comm_rank(MPI_COMM_WORLD, &rank);	/* get current process id */
	MPI_Comm_size(MPI_COMM_WORLD, &size);	/* get number of processes */

	// Must launch with 2 procs
	assert(size == 2);

	int numIter =  (1<<20); //atoi(argv[1]);


	msg = (char**) malloc(MAX_BATCH_SIZE * sizeof(char*));

	if(rank == 0){
		cout<<endl<<"batchSize"<<"\t"<<"msgSize"<<"\t"<<"designatedReceiverTime"<<"\t"<<"anyReceiverTime";
		cout<<endl<<"*********** WARMUP*****************";
	}

	// warmup
	AllocateMsgBuffer(1);
	if(rank == 0) {
		DoSendExperiment(1, 8, numIter/8);

	} else if(rank == 1) {
		DoRecvExperiment(1, 8, numIter/8);
	}	

	FreeMsgBuffer();

	if(rank == 0)
		cout<<endl<<"batchSize"<<"\t"<<"msgSize"<<"\t"<<"designatedReceiverTime"<<"\t"<<"anyReceiverTime";


	for(int msgSize = 1; msgSize <= (1<<20); msgSize = (msgSize << 1)) {
		// allocate message array
		AllocateMsgBuffer(msgSize);
		for(int batchSize = 1; batchSize <= MAX_BATCH_SIZE; batchSize = (batchSize << 1)) {
			if(rank == 0) {
				DoSendExperiment(msgSize, batchSize, numIter/batchSize);

			} else if(rank == 1) {
				DoRecvExperiment(msgSize, batchSize, numIter/batchSize);
			}
		}
		FreeMsgBuffer();
	}
	free(msg);
	MPI_Finalize();
	return 0;

}

