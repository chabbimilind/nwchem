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
        void * stackBottom;

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

        void SetStackBottom(void* bottom) {
            stackBottom = bottom;
        }
        void * GetStackBottom(){
            return stackBottom;
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

#define USE_LIBUNWIND
//#define USE_CUSTOM_UNWINDER

#ifdef USE_LIBUNWIND
    extern int REAL_FUNCTION(main)(int argc, char ** argv);
    int WRAPPED_FUNCTION(main)(int argc, char ** argv) {
        return REAL_FUNCTION(main)(argc, argv);
    }

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
#elif defined(USE_CUSTOM_UNWINDER)
#define ASM_LABEL(name)         \
    asm volatile (".globl " #name );    \
    asm volatile ( #name ":" )

    
    extern int REAL_FUNCTION(main)(int argc, char ** argv);
    extern void * main_fence1 __attribute__((weak));
    extern void * main_fence2 __attribute__((weak));
    
    /*
     *  Returns: 1 if address is within the body of the function at the
     *  bottom of the application's call stack, else 0.
     */
    int HasStackEnded(void * insPtr, void * framePtr) {
        if (&main_fence1 <= insPtr && insPtr <= &main_fence2)
            return 1;
        if (framePtr > GLOBAL_STATE.GetStackBottom())
            return 1;
        return 0;
    }

    int WRAPPED_FUNCTION(main)(int argc, char ** argv) {
        ASM_LABEL(main_fence1);
        GLOBAL_STATE.SetStackBottom(alloca(8));
        strncpy((char *) GLOBAL_STATE.GetStackBottom(), "stakbot", 8);
        return REAL_FUNCTION(main)(argc, argv);
        ASM_LABEL(main_fence2);
    }
    
    static inline uint64_t GetContextHash() {
        void ** curStackPointer = (void **) __builtin_frame_address(0);
        void * curRA = *(curStackPointer+1);
        uint64_t hash = 0;
#if 0
        if(myRank == 0)
            printf("\nUnwind Start \n");
#endif
        // Iterate over return addresses and sum them to get a hash
        while(!HasStackEnded(curRA, curStackPointer)) {
            hash += (uint64_t)curRA;
            curStackPointer = (void **) (*curStackPointer);
            curRA = *(curStackPointer+1);
        }
#if 0
        if(myRank == 0)
            printf("\nUnwind End \n");
#endif
        return hash;
    }
#endif

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
    static struct timeval mpiInitTime, mpiFinalizeTime;


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


vector<uint64_t> allCtxt;

void DumpAllCtxt(){
	if(myRank != 0)
		return;
	FILE * fp = fopen("allCtxt.txt","w");
	for(int i = 0 ; i < allCtxt.size(); i++)
		fprintf(fp, "%llu\n", allCtxt[i]);

	fclose(fp);
}


    int WRAPPED_FUNCTION(MPI_Barrier)(MPI_Comm comm) {
//HACK HACK to get the ctxts
//uint64_t t = GetContextHash();
//allCtxt.push_back(t);
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
// HACK HACK
//        atexit(DumpAllCtxt);
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);

        // Get time after statring MPI
        if(myRank == 0) {
            gettimeofday(&mpiInitTime, NULL);
        }

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
        // Print execution time
        if(myRank == 0) {
            gettimeofday(&mpiFinalizeTime, NULL);
            uint64_t span = TIME_SPENT(mpiInitTime, mpiFinalizeTime);
            printf("\n End-to-end execution time %lu \n", span);
        }
        int retVal = REAL_FUNCTION(MPI_Finalize)();
        return retVal;
    }
}


