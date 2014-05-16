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
#include <tr1/unordered_map>
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
#include<dmapp.h>
#include<mpi.h>


using namespace std;
using namespace std::tr1;

extern "C" {
    static struct timeval t1, t2;

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

    static void EnableBarrierOptimization() {
        int myRank;
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);

        if(myRank == 0) {
            gettimeofday(&t1, NULL);
            printf("\n Enabled BO\n");
        }
    }
    // fortran interface
    void enable_barrier_optimization_() {
        EnableBarrierOptimization();
    }

    static void DisableBarrierOptimization() {
        int myRank;
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);

        if(myRank == 0) {
            gettimeofday(&t2, NULL);
            uint64_t span = TIME_SPENT(t1, t2);
            printf("\n Disabled BO %lu \n", span);
        }
    }

    // fortran interface
    void disable_barrier_optimization_() {
        DisableBarrierOptimization();
    }


}
