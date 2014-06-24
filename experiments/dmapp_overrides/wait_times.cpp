// * BeginRiceCopyright *****************************************************
//
// Copyright ((c)) 2002-2014, Rice University
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// * Redistributions of source code must retain the above copyright
//   notice, this list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright
//   notice, this list of conditions and the following disclaimer in the
//   documentation and/or other materials provided with the distribution.
//
// * Neither the name of Rice University (RICE) nor the names of its
//   contributors may be used to endorse or promote products derived from
//   this software without specific prior written permission.
//
// This software is provided by RICE and contributors "as is" and any
// express or implied warranties, including, but not limited to, the
// implied warranties of merchantability and fitness for a particular
// purpose are disclaimed. In no event shall RICE or contributors be
// liable for any direct, indirect, incidental, special, exemplary, or
// consequential damages (including, but not limited to, procurement of
// substitute goods or services; loss of use, data, or profits; or
// business interruption) however caused and on any theory of liability,
// whether in contract, strict liability, or tort (including negligence
// or otherwise) arising in any way out of the use of this software, even
// if advised of the possibility of such damage.
//
// ******************************************************* EndRiceCopyright *

#include <stdio.h>
#include <execinfo.h>
#include <stdlib.h>
#include <vector>
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
#include<mpi.h>


using namespace std;

extern "C" {

#define BARRIER_FN_NAME "MPI_Barrier"

#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name
#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)
    
    static FILE* logFilePtr;
    int myRank;
    struct timeval startTime, endTime;

    vector<uint64_t> barrierTimes;
    static  void DumpBarrierTimes() {
        for(int i = 0; i < barrierTimes.size(); i++)
            fprintf(logFilePtr, "%lu,", barrierTimes[i]);
    }


    static void CloseLogFile() {
        fclose(logFilePtr);
    }

    static void CreateLogFile(int rank) {
        assert(logFilePtr == NULL);
        std::stringstream ss;
        char hostname[200];
        pid_t pid = getpid();
        ss << "LOG_" << pid << ".log";
        logFilePtr = fopen(ss.str().c_str(), "w");
    }


    extern int REAL_FUNCTION(MPI_Barrier)(MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Init)(int* argc, char** *argv);
    extern int REAL_FUNCTION(MPI_Finalize)(void);

    
    int WRAPPED_FUNCTION(MPI_Barrier)(MPI_Comm comm) {
        int retVal = MPI_SUCCESS;
        struct timeval t1, t2;
        gettimeofday(&t1, NULL);
        retVal = REAL_FUNCTION(MPI_Barrier)(comm);
        gettimeofday(&t2, NULL);
        barrierTimes.push_back(TIME_SPENT(t1,t2));
        return retVal;
    }


    int WRAPPED_FUNCTION(MPI_Init)(int* argc, char** *argv) {
        int retVal = REAL_FUNCTION(MPI_Init)(argc, argv);
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);
        CreateLogFile(myRank);
        if(myRank == 0) {
            gettimeofday(&startTime, NULL);
        }
        
        return retVal;
    }


    int WRAPPED_FUNCTION(MPI_Finalize)() {
        int retVal = REAL_FUNCTION(MPI_Finalize)();
        
        if(myRank == 0) {
            gettimeofday(&endTime, NULL);
            printf("\n Execution Time = %lu \n", TIME_SPENT(startTime, endTime));
        }

        DumpBarrierTimes();
        CloseLogFile();
        
        return retVal;
    }
}


