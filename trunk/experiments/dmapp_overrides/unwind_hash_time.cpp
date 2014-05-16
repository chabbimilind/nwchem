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
#include "barrier_deletion.h"


using namespace std;
using namespace std::tr1;

extern "C" {

#define BARRIER_FN_NAME "MPI_Barrier"
#define ALLGATHER_FN_NAME "MPI_Allgather"
#define ALLREDUCE_FN_NAME "MPI_Allreduce"

#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name

#define ALL_REDUCE_BUFFER(status) ( ((status) << 32 ) | GLOBAL_STATE.GetBarrierInstance())
#define ALL_REDUCE_GET_STATUS(buffer) ( (buffer) >> 32 )
#define ALL_REDUCE_GET_INSTANCE(buffer) ((buffer) & 0xffffffff)


#define SKIP (10)
#define PARTICIPATE (0)

//#define ENABLE_LOGGING


//#define VERBOSE

    /******** Globals variables **********/

    struct GLOBAL_STATE_t {
        unordered_map<uint64_t, uint64_t> barrierSkipCache;
        unordered_map<uint64_t, uint64_t>::iterator barrierSkipCacheIterator;
        uint64_t barrierInstance;
        uint64_t enabledBarrierInstance;
        uint64_t skippable;
        uint64_t reSync;
        uint64_t badDecison;
        uint64_t lastParticipatedBarrier;
        bool isEnabled;

        void Enable() {
            isEnabled = true;
        }
        void Disable() {
            isEnabled = false;
        }
        bool IsEnabled() {
            return isEnabled;
        }


        void SetLastParticipatedBarrier(uint64_t lpb) {
            lastParticipatedBarrier = lpb;
        }
        uint64_t GetLastParticipatedBarrier() {
            return lastParticipatedBarrier;
        }

        uint64_t IncrementBadDecision() {
            return badDecison++;
        }
        uint64_t GetBadDecision() {
            return badDecison;
        }

        uint64_t IncrementSkippable() {
            return skippable ++;
        }
        uint64_t DecrementSkippable() {
            return skippable --;
        }
        uint64_t GetSkippable() {
            return skippable;
        }

        uint64_t IncrementReSync() {
            return reSync ++;
        }
        uint64_t GetReSync() {
            return reSync;
        }

        uint64_t IncrementEnabledBarrierInstance() {
            uint64_t val = enabledBarrierInstance;

            if(IsEnabled())
                enabledBarrierInstance ++;

            return val;
        }
        uint64_t GetEnabledBarrierInstance() {
            return enabledBarrierInstance;
        }

        uint64_t IncrementBarrierInstance() {
            IncrementEnabledBarrierInstance();
            return barrierInstance ++;
        }
        uint64_t GetBarrierInstance() {
            return barrierInstance;
        }
        bool doUnwind;


    } ;
    GLOBAL_STATE_t GLOBAL_STATE;

    static int myRank = -1;
    static MPI_Op myMPIOp;

    static void PrintStats() {
        if(myRank == 0) {
            printf("\n Total Barriers = %lu, Enabled = %lu, Skippable =%lu, reSync = %lu, bad decision = %lu", GLOBAL_STATE.GetBarrierInstance(), GLOBAL_STATE.GetEnabledBarrierInstance(), GLOBAL_STATE.GetSkippable(), GLOBAL_STATE.GetReSync(), GLOBAL_STATE.GetBadDecision());
        }
    }


    static void MyMPIReductionOp(void* a, void* b, int* len, MPI_Datatype* type) {
        uint64_t a1 = *((uint64_t*)a);
        uint64_t b1 = *((uint64_t*)b);
        uint32_t statusA = ALL_REDUCE_GET_STATUS(a1);
        uint32_t statusB = ALL_REDUCE_GET_STATUS(b1);
        uint32_t instanceA = ALL_REDUCE_GET_INSTANCE(a1);
        uint32_t instanceB = ALL_REDUCE_GET_INSTANCE(b1);
        // Min of status
        uint64_t retStatus = statusA < statusB ? statusA : statusB;
        // Min of barrier instance
        uint64_t retInstance = instanceA < instanceB ? instanceA : instanceB;
        *((uint64_t*)b) = (((retStatus) << 32) | retInstance);
    }


#define UNW_LOCAL_ONLY
#include <libunwind.h>


    static inline uint64_t GetContextHash() {
        unw_cursor_t cursor;
        unw_context_t uc;
        unw_word_t ip, sp;
        bool first = true;
        unw_getcontext(&uc);
        unw_init_local(&cursor, &uc);
        uint64_t hash = 0;

        // Iterate over return addresses and sum the to get a hash
        while(unw_step(&cursor) > 0) {
            unw_get_reg(&cursor, UNW_REG_IP, &ip);
            /*if(first) {
             unw_get_reg(&cursor, UNW_REG_SP, &sp);
             first = false;
             } */
            hash += ip;
        }

        //hash  = ((hash & 0xffffffff) << (31)) | ( ((uint64_t) sp) & 0xffffffff);
        return hash;
    }


    extern int REAL_FUNCTION(MPI_Barrier)(MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Init)(int* argc, char** *argv);
    extern int REAL_FUNCTION(MPI_Finalize)(void);

    static inline void ParticipateInBarrier(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
        uint64_t recvBuf;
        uint64_t sendBuf = PARTICIPATE;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = MPI_Allreduce(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
    }

    static struct timeval t1, t2;

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)

    static void EnableBarrierOptimization() {
        if(myRank == 0) {
            gettimeofday(&t1, NULL);
            printf("\n Enabled BO\n");
        }

        GLOBAL_STATE.Enable();
    }
    // fortran interface
    void enable_barrier_optimization_() {
        EnableBarrierOptimization();
    }

    static void DisableAndCleanupBarrierOptimization() {
        if(myRank == 0) {
            printf("\n Disabled BO\n");
        }

        GLOBAL_STATE.Disable();
    }

    // fortran interface
    void disable_and_cleanup_barrier_optimization_() {
        DisableAndCleanupBarrierOptimization();
    }

    static void DisableBarrierOptimization() {
        if(myRank == 0) {
            gettimeofday(&t2, NULL);
            uint64_t span = TIME_SPENT(t1, t2);
            printf("\n Disabled BO %lu \n", span);
        }

        GLOBAL_STATE.Disable();
    }

    // fortran interface
    void disable_barrier_optimization_() {
        DisableBarrierOptimization();
    }



    int WRAPPED_FUNCTION(MPI_Barrier)(MPI_Comm comm) {
        if(GLOBAL_STATE.IsEnabled() && GLOBAL_STATE.doUnwind) {
            // unwind
            volatile uint64_t t = GetContextHash();
        }

        return  REAL_FUNCTION(MPI_Barrier)(comm);
    }


    int WRAPPED_FUNCTION(MPI_Init)(int* argc, char** *argv) {
        int retVal = REAL_FUNCTION(MPI_Init)(argc, argv);
        // Register my reduction op
        MPI_Op_create(MyMPIReductionOp, 1 /*commute*/, &myMPIOp);
        atexit(PrintStats);
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);
        // Read env whether to do all reduce or barrier
        char* val = getenv("NWCHEM_BARRIER_TYPE");

        if(val) {
            if(strcmp(val, "unwind") == 0) {
                GLOBAL_STATE.doUnwind = true;
            } else {
                GLOBAL_STATE.doUnwind = false;
            }
        }

        return retVal;
    }


    int WRAPPED_FUNCTION(MPI_Finalize)() {
        int retVal = REAL_FUNCTION(MPI_Finalize)();
        return retVal;
    }
}


