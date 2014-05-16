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


#define BARRIER_TRACE
#define VERBOSE

    /******** Globals variables **********/

    struct GLOBAL_STATE_t {
        unordered_map<uint64_t, uint64_t> barrierSkipCache;
        unordered_map<uint64_t, uint64_t>::iterator barrierSkipCacheIterator;
        uint64_t barrierInstance;
        uint64_t skippable;
        uint64_t reSync;
        uint64_t badDecison;
        uint64_t lastParticipatedBarrier;

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

        uint64_t IncrementBarrierInstance() {
            return barrierInstance ++;
        }
        uint64_t GetBarrierInstance() {
            return barrierInstance;
        }



    } ;
    GLOBAL_STATE_t GLOBAL_STATE;

    static int myRank = -1;
    static MPI_Op myMPIOp;


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


    static void DumpRedundancyMap();

    static FILE* fp;


    __attribute__((destructor))
    static void OnExit() {
        if(myRank == 0) {
            printf("\n Total Barriers = %lu, Skippable =%lu, reSync = %lu, bad decision = %lu", GLOBAL_STATE.GetBarrierInstance(), GLOBAL_STATE.GetSkippable(), GLOBAL_STATE.GetReSync(), GLOBAL_STATE.GetBadDecision());
#ifdef VERBOSE
            //        DumpRedundancyMap();
#endif
        }
    }




    __thread bool gAccessedRemoteData;

#define SKIP (10)
#define PARTICIPATE (0)

#define USE_LIBUNWIND
    /******** Function definitions **********/

#if defined(SIMPLE_CONTEXT)
    inline uint64_t GetContextHash() {
        uint64_t returnAddress = (uint64_t) __builtin_return_address(0);
        uint64_t stackPointer = (uint64_t) __builtin_frame_address(0);
        uint64_t key = ((returnAddress & 0xffffffff) << (31)) | (stackPointer & 0xffffffff);
        return key;
    }
#elif defined(USE_LIBUNWIND)
#define BUMP_BT
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



    struct RedundancyKey {
        uint64_t lastBarrier;
        uint64_t curBarrier;
    };

    struct Hasher {
        size_t operator()(RedundancyKey const& s) const {
            size_t hash = s.lastBarrier + s.curBarrier;
            return hash;
        }
    };

    struct EqualFn {
        bool operator()(RedundancyKey const& a, RedundancyKey const& b) const {
            return a.lastBarrier == b.lastBarrier && a.curBarrier == b.curBarrier;
        }
    };

    static unordered_map<uint64_t, vector<void*> > backtraceMap;
    typedef unordered_map<RedundancyKey, uint64_t, Hasher, EqualFn> RedundancyMap_t;
    static RedundancyMap_t redundancyMap;


    static inline uint64_t GetContextHashWithBackTrace() {
        unw_cursor_t cursor;
        unw_context_t uc;
        unw_word_t ip, sp;
        bool first = true;
        unw_getcontext(&uc);
        unw_init_local(&cursor, &uc);
        uint64_t hash = 0;
        vector<void*> btVec;

        while(unw_step(&cursor) > 0) {
            unw_get_reg(&cursor, UNW_REG_IP, &ip);
            /*if(first) {
             unw_get_reg(&cursor, UNW_REG_SP, &sp);
             first = false;
             } */
            btVec.push_back((void*) ip);
            hash += ip;
        }

        // if this hash is never seen before, record it.
        unordered_map<uint64_t, vector<void*> >::iterator  ii = backtraceMap.find(hash);

        if(ii == backtraceMap.end()) {
            backtraceMap[hash] = btVec;
            //if (myRank ==0) printf("\n New Key in backtraceMap vec = %lx: %d\n",hash, btVec.size()) ;
        }

        //hash  = ((hash & 0xffffffff) << (31)) | ( ((uint64_t) sp) & 0xffffffff);
        return  hash;
    }

    static inline void RecordInRedundancyMap(uint64_t curBarrierHash) {
        RedundancyKey key = {GLOBAL_STATE.GetLastParticipatedBarrier(), curBarrierHash};
        RedundancyMap_t::iterator  ri = redundancyMap.find(key);

        if(ri  != redundancyMap.end()) {
            ri->second ++;
            /*
             if (myRank ==0) {
             uint64_t lpb = ri->first.lastBarrier;
             uint64_t cb = ri->first.curBarrier;
             printf("\n lpb = %lx cb = %lx sec = %lu\n", lpb, cb, ri->second);
             }
             */
        } else {
            if(myRank == 0) {
                //printf("\n New Key in redundancy map = %lx : %lx\n", key.lastBarrier, key.curBarrier);
            }

            redundancyMap[key] = 1;
        }
    }


    static void DumpStack(uint64_t key) {
        assert(backtraceMap.find(key) != backtraceMap.end());
        vector <void*>& stack = backtraceMap[key];

        //printf("\n %d", stack.size());
        for(int i = 0; i < stack.size(); i++)
            printf("\t %lx", stack[i]);
    }

    static void DumpRedundancyMap() {
        for(RedundancyMap_t::iterator ri = redundancyMap.begin(); ri != redundancyMap.end(); ri++) {
            uint64_t lpb = ri->first.lastBarrier;
            uint64_t cb = ri->first.curBarrier;
            //printf("\n lpb = %lx cb = %lx\n", lpb, cb);
            printf("\n ================\n");
            printf("%lu : ", ri->second);

            if(lpb != 0)
                DumpStack(lpb);
            else
                printf(" 0 ");

            printf(" : ");
            DumpStack(cb);
        }
    }


    static inline void PrintBT() {
        unw_cursor_t cursor;
        unw_context_t uc;
        unw_word_t ip, sp;
        unw_getcontext(&uc);
        unw_init_local(&cursor, &uc);
        printf("\n --------------- \n");

        while(unw_step(&cursor) > 0) {
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
    static void* array[BT_SIZE];
    static inline uint64_t GetContextHash() {
        size_t size;
        size_t i;
        size = backtrace(array, BT_SIZE);
        uint64_t hash = 0;

        for(i = 0; i < size; i++)
            hash += (uint64_t) array[i];

        return hash;
    }

    static void PrintBT() {
        size_t size;
        size_t i;
        size = backtrace(array, BT_SIZE);
        backtrace_symbols_fd(array, size, 1);
    }

#endif




    static  void DumpStack2(uint64_t key) {
        assert(backtraceMap.find(key) != backtraceMap.end());
        assert(fp);
        vector <void*>& stack = backtraceMap[key];

        for(int i = 0; i < stack.size(); i++)
            fprintf(fp, "\t %lx", stack[i]);
    }


    static void OnEnd() {
        if(fp)
            fclose(fp);
    }


    static void Log(MPI_Comm comm, uint64_t key, string s, uint64_t barInst, int status) {
        if(fp == NULL) {
            // construct one
            std::stringstream ss;
            char hostname[200];
            pid_t pid = getpid();
            ss << "LOG_" << pid << ".log";
            fp = fopen(ss.str().c_str(), "w");
        }

        int size;
        MPI_Comm_size(comm, &size);
        int rank;
        MPI_Comm_rank(comm, &rank);
        fprintf(fp, "\n SIZE= %d : RANK = %d: BARINST = %lu, KEY = %lu, STATUS = %d, %s at ", size, rank, barInst, key, status, s.c_str());
        DumpStack2(key);
    }

#ifdef BARRIER_TRACE
    static FILE* barrierTraceFP;
    static void CloseBarrierTrace() {
        fclose(barrierTraceFP);
    }
    static void OpenBarrierTrace() {
        if(barrierTraceFP == NULL) {
            // construct one
            std::stringstream ss;
            char hostname[200];
            pid_t pid = getpid();
            int rank;
            MPI_Comm_rank(MPI_COMM_WORLD, &rank);
            ss << "BARRIER_TRACE_" << pid << "_" << rank << ".log";
            barrierTraceFP = fopen(ss.str().c_str(), "w");
        }
    }
    void PrintContextVector(char* s) {
        unw_cursor_t cursor;
        unw_context_t uc;
        unw_word_t ip, sp;
        unw_getcontext(&uc);
        unw_init_local(&cursor, &uc);

        if(barrierTraceFP)
            fprintf(barrierTraceFP, "\n %s", s);

        while(unw_step(&cursor) > 0) {
            unw_get_reg(&cursor, UNW_REG_IP, &ip);

            if(barrierTraceFP)
                fprintf(barrierTraceFP, "\t %lx", ip);
        }

        if(barrierTraceFP)
            fprintf(barrierTraceFP, "\n");
    }
    static void DumpBarrierTrace(uint64_t instance, uint64_t key, string decison, int remoteOps) {
        assert(backtraceMap.find(key) != backtraceMap.end());
        assert(barrierTraceFP);
        vector <void*>& stack = backtraceMap[key];
        fprintf(barrierTraceFP, "\n Instance: %lu, Decison=%s, remoteOps=%d\n", instance, decison.c_str(), remoteOps);

        for(int i = 0; i < stack.size(); i++)
            fprintf(barrierTraceFP, "\t %lx", stack[i]);
    }

#endif


    extern int REAL_FUNCTION(MPI_Barrier)(MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Bcast)(void* buffer, int count, MPI_Datatype datatype, int root, MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allgather)(const void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allreduce)(const void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);



    static inline void ParticipateInBarrier(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
        Log(comm, key, "Participating:", curBarrierInstance, gAccessedRemoteData);
        // We have already decided to participate for this barrier
        GLOBAL_STATE.SetLastParticipatedBarrier(key);
        /*#ifdef BUMP_BT
         if(myRank == 0)
         PrintBT();
         #endif
         */
        uint64_t recvBuf;
        //uint64_t sendBuf = curBarrierInstance;
        uint64_t sendBuf = PARTICIPATE;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);

        // Bad state! Somebody decided to skip! Should never happen.
        if(ALL_REDUCE_GET_INSTANCE(recvBuf)  != GLOBAL_STATE.GetBarrierInstance()) {
            printf("\n sendBuf = %lx, recvBuf = %lx, ALL_REDUCE_GET_INSTANCE(recvBuf) = %lx, GLOBAL_STATE.GetBarrierInstance() = %lx", sendBuf, recvBuf, ALL_REDUCE_GET_INSTANCE(recvBuf), GLOBAL_STATE.GetBarrierInstance());
        }

#ifdef BARRIER_TRACE
        DumpBarrierTrace(curBarrierInstance, key, "PARTICIPATE", gAccessedRemoteData);
#endif
        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());
        //assert(recvBuf == curBarrierInstance);
        // Exit
        gAccessedRemoteData = false;
    }


    static inline void SkipTheBarrier(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
#ifdef BARRIER_TRACE
        DumpBarrierTrace(curBarrierInstance, key, "SKIP", gAccessedRemoteData);
#endif

        // We had decided to skip this barrier
        if(!gAccessedRemoteData) {
            // The decision still holds good.
            Log(comm, key, "Skipping:", curBarrierInstance, gAccessedRemoteData);
            GLOBAL_STATE.IncrementSkippable();
#ifdef VERBOSE
            RecordInRedundancyMap(key);
#endif
            /*                         #ifdef BUMP_BT
             if(myRank == 0)
             PrintBT();
             #endif
             */
            //#define BARRIER_DEBUG
#ifdef BARRIER_DEBUG
            uint64_t recvBuf;
            //uint64_t sendBuf = curBarrierInstance;
            uint64_t sendBuf = SKIP;
            sendBuf = ALL_REDUCE_BUFFER(sendBuf);
            // Ensure the assumption is not violated by any process
            retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
            assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());
            int size;
            MPI_Comm_size(comm, &size);

            if(ALL_REDUCE_GET_STATUS(recvBuf) == SKIP) {
                //GLOBAL_STATE.skippable++;
            } else {
                GLOBAL_STATE.DecrementSkippable();
                GLOBAL_STATE.IncrementBadDecision();

                if(myRank == 0) {
                    printf("\n Bad decision at") ;
                    PrintBT();
                }
            }

#endif
        } else {
            Log(comm, key, "Breaking:", curBarrierInstance, gAccessedRemoteData);
            // I am breaking my consensus... so what if all are breaking we are still fine.
            uint64_t recvBuf;
            //uint64_t sendBuf = curBarrierInstance;
            uint64_t sendBuf = PARTICIPATE;
            sendBuf = ALL_REDUCE_BUFFER(sendBuf);
            retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);

            if(ALL_REDUCE_GET_INSTANCE(recvBuf)  != GLOBAL_STATE.GetBarrierInstance()) {
                printf("\n sendBuf = %lx, recvBuf = %lx, ALL_REDUCE_GET_INSTANCE(recvBuf) = %lx, GLOBAL_STATE.GetBarrierInstance() = %lx", sendBuf, recvBuf, ALL_REDUCE_GET_INSTANCE(recvBuf), GLOBAL_STATE.GetBarrierInstance());
            }

            assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());

            if(ALL_REDUCE_GET_STATUS(recvBuf) != PARTICIPATE) {
                // This is the worst place to be in. We can't handle this as yet.
                if(myRank == 0) {
                    printf("\n Bad decision at") ;
                    PrintBT();
                }

                GLOBAL_STATE.IncrementBadDecision();
            } else {
                // All processes broke the code, so we are back in sync.
                GLOBAL_STATE.IncrementReSync();
            }

            // Exit
            gAccessedRemoteData = false;
            //assert(recvBuf == curBarrierInstance);
        }
    }

    static inline void ContinueDecisionProcess(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
#ifdef BARRIER_TRACE
        DumpBarrierTrace(curBarrierInstance, key, "DECISION_PROCESS", gAccessedRemoteData);
#endif
        Log(comm, key, "Deciding:", curBarrierInstance, gAccessedRemoteData);
        // in decison process ... do all reduce
        uint64_t recvBuf;
        uint64_t newVal = val + 1;
        uint64_t sendBuf = gAccessedRemoteData ? PARTICIPATE : newVal;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());

        if(ALL_REDUCE_GET_STATUS(recvBuf) == newVal) {
            GLOBAL_STATE.barrierSkipCache[key] = newVal;
        } else {
            GLOBAL_STATE.barrierSkipCache[key] = PARTICIPATE;
            Log(comm, key, "VetoInDecison:", curBarrierInstance, gAccessedRemoteData);
        }
    }


    static inline void HandleFirstVisit(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, int& retVal) {
#ifdef BARRIER_TRACE
        DumpBarrierTrace(curBarrierInstance, key, "FIRST_VISIT", gAccessedRemoteData);
#endif
        Log(comm, key, "Firsttime:", curBarrierInstance, gAccessedRemoteData);
        // first visit ... do all reduce
        uint64_t recvBuf;
        uint64_t sendBuf = gAccessedRemoteData ? PARTICIPATE : 1;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());
        GLOBAL_STATE.barrierSkipCache[key] = ALL_REDUCE_GET_STATUS(recvBuf);

        if(ALL_REDUCE_GET_STATUS(recvBuf) == PARTICIPATE) {
            gAccessedRemoteData = false;
            Log(comm, key, "VetoOnFirstRound:", curBarrierInstance, gAccessedRemoteData);
        }
    }


    int WRAPPED_FUNCTION(MPI_Barrier)(MPI_Comm comm) {
        if(myRank == -1) {
            // Get my rank
            MPI_Comm_rank(comm, &myRank);
            // Register my reduction op
            MPI_Op_create(MyMPIReductionOp, 1 /*commute*/, &myMPIOp);
#ifdef VERBOSE

            // Register on exit function
            if(myRank == 0)
                atexit(DumpRedundancyMap);

#endif
#ifdef BARRIER_TRACE
            OpenBarrierTrace();
            // Register on exit function
            atexit(CloseBarrierTrace);
#endif
            atexit(OnEnd);
        }

        int retVal = MPI_SUCCESS;
        // increment the barrrier instance
        uint64_t curBarrierInstance = GLOBAL_STATE.IncrementBarrierInstance();
#ifdef VERBOSE
        uint64_t key = GetContextHashWithBackTrace();
#else
        uint64_t key = GetContextHash();
#endif
        // Is this barrier previously seen?
        GLOBAL_STATE.barrierSkipCacheIterator = GLOBAL_STATE.barrierSkipCache.find(key);

        // ENtry
        if(GLOBAL_STATE.barrierSkipCacheIterator != GLOBAL_STATE.barrierSkipCache.end()) {
            uint64_t val = GLOBAL_STATE.barrierSkipCacheIterator->second;

            switch(val) {
            case PARTICIPATE: {
                ParticipateInBarrier(comm, key, curBarrierInstance, val, retVal);
                break;
            }

            case SKIP: {
                SkipTheBarrier(comm, key, curBarrierInstance, val, retVal);
                break;
            }

            default: {
                ContinueDecisionProcess(comm, key, curBarrierInstance, val, retVal);
                break;
            }
            }
        } else {
            HandleFirstVisit(comm, key, curBarrierInstance, retVal);
        }

        return retVal;
    }


    int WRAPPED_FUNCTION(MPI_Allgather)(const void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm) {
        int retVal = REAL_FUNCTION(MPI_Allgather)(sendbuf,  sendcount,  sendtype, recvbuf,  recvcount,  recvtype, comm);
        /*
        #ifdef VERBOSE
        uint64_t key = GetContextHashWithBackTrace();
        GLOBAL_STATE.SetLastParticipatedBarrier(key);
        Log(comm, key, "MPI_Allgather:");
        #endif

        // Exit
        gAccessedRemoteData = false; */
        return retVal;
    }

    int WRAPPED_FUNCTION(MPI_Bcast)(void* buffer, int count, MPI_Datatype datatype, int root, MPI_Comm comm) {
        int retVal = REAL_FUNCTION(MPI_Bcast)(buffer, count, datatype, root, comm);
        /*
        #ifdef VERBOSE
        uint64_t key = GetContextHashWithBackTrace();
        GLOBAL_STATE.SetLastParticipatedBarrier(key);
        Log(comm, key, "MPI_Bcast:");
        #endif
        // Exit
        gAccessedRemoteData = false; */
        return retVal;
    }


    int WRAPPED_FUNCTION(MPI_Allreduce)(const void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm) {
        int retVal = REAL_FUNCTION(MPI_Allreduce)(sendbuf, recvbuf, count, datatype,  op,  comm);
        /*
        #ifdef VERBOSE
                uint64_t key = GetContextHashWithBackTrace();
                GLOBAL_STATE.SetLastParticipatedBarrier(key);
                Log(comm, key, "MPI_Allreduce:");
        #endif
                // Exit
                gAccessedRemoteData = false; */
        return retVal;
    }
}


