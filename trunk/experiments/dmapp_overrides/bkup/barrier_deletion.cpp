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
    
#define ALL_REDUCE_BUFFER(status) ( ((status) << 32 ) | GLOBAL_STATE.barrierInstance)
#define ALL_REDUCE_GET_STATUS(buffer) ( (buffer) >> 32 )
#define ALL_REDUCE_GET_INSTANCE(buffer) ((buffer) & 0xffffffff)
    
    
    /******** Globals variables **********/
    
    struct GLOBAL_STATE_t {
        unordered_map<uint64_t, uint64_t> barrierSkipCache;
        unordered_map<uint64_t, uint64_t>::iterator barrierSkipCacheIterator;
        uint64_t barrierInstance;
        uint64_t skippable;
        uint64_t reSync;
        uint64_t badDecison;
        
    } ;
    GLOBAL_STATE_t GLOBAL_STATE;
    
    static int myRank = -1;
    static MPI_Op myMPIOp;
    
    
    static void MyUserFn(void * a, void * b, int * len, MPI_Datatype * type) {
        uint64_t a1 = *((uint64_t*)a);
        uint64_t b1 = *((uint64_t*)b);
        uint32_t statusA = ALL_REDUCE_GET_STATUS(a1);
        uint32_t statusB = ALL_REDUCE_GET_STATUS(b1);
        
        uint32_t instanceA = ALL_REDUCE_GET_INSTANCE(a1);
        uint32_t instanceB = ALL_REDUCE_GET_INSTANCE(b1);
        
        uint64_t retStatus = statusA < statusB ? statusA : statusB;
        uint64_t retInstance = instanceA < instanceB ? instanceA : instanceB;
        *((uint64_t *)b) =  (((retStatus) << 32 ) | retInstance);
    }
    
    
    
    __attribute__((destructor))
    void OnExit(){
        if(myRank == 0){
            printf("\n Total Barriers = %lu, Skippable =%lu, reSync = %lu, bad decision = %lu", GLOBAL_STATE.barrierInstance, GLOBAL_STATE.skippable, GLOBAL_STATE.reSync, GLOBAL_STATE.badDecison);
        }
    }
    
    bool gAccessedRemoteData;
    
#define SKIP (10)
#define PARTICIPATE (0)
    
#define USE_LIBUNWIND
    /******** Function definitions **********/
    
#if defined(SIMPLE_CONTEXT)
    inline uint64_t GetContextHash(){
        uint64_t returnAddress = (uint64_t) __builtin_return_address(0);
        uint64_t stackPointer = (uint64_t) __builtin_frame_address(0);
        uint64_t key = ((returnAddress & 0xffffffff) << (31)) | (stackPointer & 0xffffffff);
        return key;
    }
#elif defined(USE_LIBUNWIND)
#define BUMP_BT
#define UNW_LOCAL_ONLY
#include <libunwind.h>
    inline uint64_t GetContextHash(){
        
	    unw_cursor_t cursor; unw_context_t uc;
	    unw_word_t ip, sp;
	    bool first = true;
	    unw_getcontext(&uc);
	    unw_init_local(&cursor, &uc);
	    uint64_t hash = 0;
	    while (unw_step(&cursor) > 0) {
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
    void PrintBT(){
        unw_cursor_t cursor; unw_context_t uc;
        unw_word_t ip, sp;
        
        unw_getcontext(&uc);
        unw_init_local(&cursor, &uc);
        printf("\n --------------- \n");
        while (unw_step(&cursor) > 0) {
            unw_get_reg(&cursor, UNW_REG_IP, &ip);
		    printf(" %lx", ip);
            //        std::stringstream command;
            //                command << "/usr/bin/addr2line -C -f -e " << " /global/homes/m/mc29/nwchem-6.3_opt/bin/LINUX64/nwchem " << " " << std::hex << ip;
            //                      system(command.str().c_str());
        }
        printf("\n ---------------\n");
    }
    
    
#else
#define BUMP_BT
#define BT_SIZE (1000)
    void * array[BT_SIZE];
    inline uint64_t GetContextHash(){
        size_t size;
        size_t i;
        
        size = backtrace (array, BT_SIZE);
        uint64_t hash = 0;
        for (i = 0; i < size; i++)
            hash += (uint64_t) array[i];
        
        return hash;
    }
    
    void PrintBT(){
        size_t size;
        size_t i;
        
        size = backtrace (array, BT_SIZE);
        backtrace_symbols_fd(array, size, 1);
    }
    
#endif
    
    
    
    extern int REAL_FUNCTION(MPI_Barrier) (MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allgather) (const void *sendbuf, int sendcount, MPI_Datatype sendtype,
                                             void *recvbuf, int recvcount, MPI_Datatype recvtype,
                                             MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allreduce) (const void *sendbuf, void *recvbuf, int count,
                                             MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
    int WRAPPED_FUNCTION(MPI_Barrier) (MPI_Comm comm){
        //return REAL_FUNCTION(MPI_Barrier) (comm);
        if(myRank == -1) {
            MPI_Comm_rank(comm, &myRank );
            MPI_Op_create(MyUserFn, 1 /*commute*/, &myMPIOp);
        }
        
        int retVal = MPI_SUCCESS;
        uint64_t curBarrierInstance = GLOBAL_STATE.barrierInstance++;
        uint64_t key = GetContextHash();
        
        GLOBAL_STATE.barrierSkipCacheIterator = GLOBAL_STATE.barrierSkipCache.find(key);
        
        
        // ENtry
        if(GLOBAL_STATE.barrierSkipCacheIterator != GLOBAL_STATE.barrierSkipCache.end()){
            uint64_t val = GLOBAL_STATE.barrierSkipCacheIterator->second;
            switch(val){
                case PARTICIPATE: {
                    /*#ifdef BUMP_BT
                     if(myRank == 0)
                     PrintBT();
                     #endif
                     */
                    uint64_t recvBuf;
                    //uint64_t sendBuf = curBarrierInstance;
                    uint64_t sendBuf = PARTICIPATE;
                    retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, MPI_MIN, comm);
                    //assert(recvBuf == curBarrierInstance);
                    break;
                }
                case SKIP:{
                    if(!gAccessedRemoteData){
                        GLOBAL_STATE.skippable++;
                        /*
                         #ifdef BUMP_BT
                         if(myRank == 0)
                         PrintBT();
                         #endif
                         */
#define BARRIER_DEBUG
#ifdef BARRIER_DEBUG
                        uint64_t recvBuf;
                        //uint64_t sendBuf = curBarrierInstance;
                        uint64_t sendBuf = SKIP;
                        sendBuf = ALL_REDUCE_BUFFER(sendBuf);

                        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
                        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.barrierInstance);

                        int size;
                        MPI_Comm_size(comm, &size);
                        if(ALL_REDUCE_GET_STATUS(recvBuf) == SKIP) {
                            //GLOBAL_STATE.skippable++;
                        } else {
                            GLOBAL_STATE.skippable--;
                            GLOBAL_STATE.badDecison++;
                            if(myRank == 0) {
                                printf("\n Bad decision at") ;
                                PrintBT();
                            }
                        }
#endif
                        
                    } else {
                        uint64_t recvBuf;
                        //uint64_t sendBuf = curBarrierInstance;
                        uint64_t sendBuf = PARTICIPATE;
                        sendBuf = ALL_REDUCE_BUFFER(sendBuf);

                        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
                        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.barrierInstance);

                        if (ALL_REDUCE_GET_STATUS(recvBuf) != PARTICIPATE) {
                            if(myRank == 0) {
                                printf("\n Bad decision at") ;
                                PrintBT();
                            }
                            GLOBAL_STATE.badDecison++;
                        } else {
                            GLOBAL_STATE.reSync++;
                        }
                        //assert(recvBuf == curBarrierInstance);
                    }
                    break;
                }
                default: {
                    // in decison process ... do all reduce
                    uint64_t recvBuf;
                    uint64_t newVal = val + 1;
                    uint64_t sendBuf = gAccessedRemoteData? PARTICIPATE : newVal;
                    sendBuf = ALL_REDUCE_BUFFER(sendBuf);

                    retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);

                    assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.barrierInstance);
                    
                    if ( ALL_REDUCE_GET_STATUS(recvBuf) == newVal) {
                        GLOBAL_STATE.barrierSkipCache[key] = newVal;
                    } else {
                        GLOBAL_STATE.barrierSkipCache[key] = PARTICIPATE;
                    }
                    
                }
            }
        } else {
            // first visit ... do all reduce
            uint64_t recvBuf;
            uint64_t sendBuf = gAccessedRemoteData? PARTICIPATE : 1;
            
            sendBuf = ALL_REDUCE_BUFFER(sendBuf);
            retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
            assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.barrierInstance);
            
            GLOBAL_STATE.barrierSkipCache[key] = ALL_REDUCE_GET_STATUS(recvBuf);
        }
        
        
        // Exit
        gAccessedRemoteData = false;
        return retVal;
        
    }
    
    
    int WRAPPED_FUNCTION(MPI_Allgather) (const void *sendbuf, int sendcount, MPI_Datatype sendtype,
                                         void *recvbuf, int recvcount, MPI_Datatype recvtype,
                                         MPI_Comm comm) {
        int retVal = REAL_FUNCTION(MPI_Allgather) ( sendbuf,  sendcount,  sendtype, recvbuf,  recvcount,  recvtype, comm);
        // Exit
        gAccessedRemoteData = false;
        return retVal;
        
    }
    
    
    int WRAPPED_FUNCTION(MPI_Allreduce) (const void *sendbuf, void *recvbuf, int count,
                                         MPI_Datatype datatype, MPI_Op op, MPI_Comm comm) {
        int retVal = REAL_FUNCTION(MPI_Allreduce) (sendbuf, recvbuf, count, datatype,  op,  comm);
        // Exit
        gAccessedRemoteData = false;
        return retVal;
        
    }
}


