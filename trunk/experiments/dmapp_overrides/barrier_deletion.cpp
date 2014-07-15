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
#include <alloca.h>
#include <google/dense_hash_map>
#include "barrier_deletion.h"

#define UNW_LOCAL_ONLY
#include <libunwind.h>


using namespace std;
using namespace std::tr1;
using google::dense_hash_map;

extern "C" {

#define BARRIER_FN_NAME "MPI_Barrier"
#define ALLGATHER_FN_NAME "MPI_Allgather"
#define ALLREDUCE_FN_NAME "MPI_Allreduce"

#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name

#define ALL_REDUCE_BUFFER(status) ( ((status) << 32 ) | GLOBAL_STATE.GetBarrierInstance())
#define ALL_REDUCE_GET_STATUS(buffer) ( (buffer) >> 32 )
#define ALL_REDUCE_GET_INSTANCE(buffer) ((buffer) & 0xffffffff)


//#define ENABLE_LOGGING

//#define ENABLE_REPLAY

//#define VERBOSE

    /******** Globals variables **********/
    
#ifdef ENABLE_REPLAY
    enum REPLAY_MODE {REPLAY_MODE_RECORD, REPLAY_MODE_REPLAY};
#define REPLAY_SKIP 'S'
#define REPLAY_PARTICIPATE 'P'
#endif
    
    struct GLOBAL_STATE_t {
        dense_hash_map<uint64_t, uint64_t> barrierSkipCache;
        dense_hash_map<uint64_t, uint64_t>::iterator barrierSkipCacheIterator;
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
#ifdef ENABLE_REPLAY
        REPLAY_MODE replayMode;
        void SetReplayMode(REPLAY_MODE mode){
            replayMode = mode;
        }
        REPLAY_MODE GetReplayMode(){
            return replayMode;
        }
#endif

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

    static void PrintStats() {
        if(myRank == 0) {
            printf("\n Total Barriers = %lu, Enabled = %lu, Skippable =%lu, reSync = %lu, bad decision = %lu", GLOBAL_STATE.GetBarrierInstance(), GLOBAL_STATE.GetEnabledBarrierInstance(), GLOBAL_STATE.GetSkippable(), GLOBAL_STATE.GetReSync(), GLOBAL_STATE.GetBadDecision());
#ifdef VERBOSE
            //        DumpRedundancyMap();
#endif
        }
    }
    __thread bool gAccessedRemoteData;
    __thread int  gDisableAnalysis = 0;

#define SKIP (10)
#define PARTICIPATE (0)

#define USE_LIBUNWIND
//#define USE_CUSTOM_UNWINDER
    
    /******** Function definitions **********/

#if defined(SIMPLE_CONTEXT)
    inline uint64_t GetContextHash() {
	assert(0 && "No longer maintained. Dont call me");
        uint64_t returnAddress = (uint64_t) __builtin_return_address(0);
        uint64_t stackPointer = (uint64_t) __builtin_frame_address(0);
        uint64_t key = ((returnAddress & 0xffffffff) << (31)) | (stackPointer & 0xffffffff);
        return key;
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
	    /* better hashing provided by Wim */
            hash += (uint64_t)curRA;
            hash += (hash << 10); 
            hash ^= (hash >> 6);

            curStackPointer = (void **) (*curStackPointer);
            curRA = *(curStackPointer+1);
        }
        hash += (hash << 3); 
        hash ^= (hash >> 11); 
        hash += (hash << 15);
#if 0
        if(myRank == 0)
            printf("\nUnwind End \n");
#endif
        return hash;
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

    
    
#elif defined(USE_LIBUNWIND)
#define BUMP_BT

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

        // Iterate over return addresses and sum them to get a hash
        while(unw_step(&cursor) > 0) {
            unw_get_reg(&cursor, UNW_REG_IP, &ip);
            /*if(first) {
             unw_get_reg(&cursor, UNW_REG_SP, &sp);
             first = false;
             } */
            hash += ip;
            hash += (hash << 10); 
            hash ^= (hash >> 6);
        }
        hash += (hash << 3); 
        hash ^= (hash >> 11); 
        hash += (hash << 15);
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


#ifdef ENABLE_LOGGING
    static FILE* logFilePtr;
    static  void LogStackTrace(uint64_t key) {
        assert(backtraceMap.find(key) != backtraceMap.end());
        assert(logFilePtr);
        vector <void*>& stack = backtraceMap[key];

        for(int i = 0; i < stack.size(); i++)
            fprintf(logFilePtr, "\t %lx", stack[i]);
    }


    static void CloseLogFile() {
        if(logFilePtr)
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

    static void Log(MPI_Comm comm, uint64_t key, string s, uint64_t barInst, int status) {
        int size;
        MPI_Comm_size(comm, &size);
        int rank;
        MPI_Comm_rank(comm, &rank);
        fprintf(logFilePtr, "\n SIZE= %d : RANK = %d: BARINST = %lu, KEY = %lu, STATUS = %d, %s at ", size, rank, barInst, key, status, s.c_str());
        LogStackTrace(key);
    }
#else
    static void DumpStack2(uint64_t key) {}
    static void CloseLogFile() {}
    static void CreateLogFile(int rank) {}
    static void Log(MPI_Comm comm, uint64_t key, string s, uint64_t barInst, int status) {}
#endif

    extern int REAL_FUNCTION(MPI_Barrier)(MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Bcast)(void* buffer, int count, MPI_Datatype datatype, int root, MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allgather)(const void* sendbuf, int sendcount, MPI_Datatype sendtype, void* recvbuf, int recvcount, MPI_Datatype recvtype, MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Allreduce)(const void* sendbuf, void* recvbuf, int count, MPI_Datatype datatype, MPI_Op op, MPI_Comm comm);
    extern int REAL_FUNCTION(MPI_Init)(int* argc, char** *argv);
    extern int REAL_FUNCTION(MPI_Finalize)(void);

    static inline void ParticipateInBarrier(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
        Log(comm, key, "Participating:", curBarrierInstance, gAccessedRemoteData);
        // Force a dmapp sync here
        dmapp_return_t t = dmapp_gsync_wait();
        assert(t == DMAPP_RC_SUCCESS);
        // We have already decided to participate for this barrier
        GLOBAL_STATE.SetLastParticipatedBarrier(key);
        uint64_t recvBuf;
        uint64_t sendBuf = PARTICIPATE;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);

        // Bad state! Somebody decided to skip! Should never happen.
        if(ALL_REDUCE_GET_INSTANCE(recvBuf)  != GLOBAL_STATE.GetBarrierInstance()) {
            printf("\n sendBuf = %lx, recvBuf = %lx, ALL_REDUCE_GET_INSTANCE(recvBuf) = %lx, GLOBAL_STATE.GetBarrierInstance() = %lx", sendBuf, recvBuf, ALL_REDUCE_GET_INSTANCE(recvBuf), GLOBAL_STATE.GetBarrierInstance());
        }

        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());
        //assert(recvBuf == curBarrierInstance);
        // Exit
        gAccessedRemoteData = false;
    }


    static inline void SkipTheBarrier(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, uint64_t val, int& retVal) {
        // We had decided to skip this barrier
        if(!gAccessedRemoteData) {
            // The decision still holds good.
            Log(comm, key, "Skipping:", curBarrierInstance, gAccessedRemoteData);
            GLOBAL_STATE.IncrementSkippable();
#ifdef VERBOSE
            RecordInRedundancyMap(key);
#endif

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
        Log(comm, key, "Deciding:", curBarrierInstance, gAccessedRemoteData);
        // in decison process ... do all reduce
        uint64_t recvBuf;
        uint64_t newVal = val + 1;
        uint64_t sendBuf = gAccessedRemoteData ? PARTICIPATE : newVal;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);
        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());

        if(ALL_REDUCE_GET_STATUS(recvBuf) == newVal && ! gDisableAnalysis) {
            GLOBAL_STATE.barrierSkipCache[key] = newVal;
        } else {
            GLOBAL_STATE.barrierSkipCache[key] = PARTICIPATE;
            Log(comm, key, "VetoInDecison:", curBarrierInstance, gAccessedRemoteData);
        }
    }


    static inline void HandleFirstVisit(MPI_Comm comm, uint64_t key, uint64_t curBarrierInstance, int& retVal) {
        Log(comm, key, "Firsttime:", curBarrierInstance, gAccessedRemoteData);
        // first visit ... do all reduce
        uint64_t recvBuf;
        uint64_t sendBuf = gAccessedRemoteData ? PARTICIPATE : 1;
        sendBuf = ALL_REDUCE_BUFFER(sendBuf);
        retVal = REAL_FUNCTION(MPI_Allreduce)(&sendBuf, &recvBuf, 1, MPI_UNSIGNED_LONG, myMPIOp, comm);

        if(ALL_REDUCE_GET_INSTANCE(recvBuf)  != GLOBAL_STATE.GetBarrierInstance()) {
            printf("\n sendBuf = %lx, recvBuf = %lx, ALL_REDUCE_GET_INSTANCE(recvBuf) = %lx, GLOBAL_STATE.GetBarrierInstance() = %lx", sendBuf, recvBuf, ALL_REDUCE_GET_INSTANCE(recvBuf), GLOBAL_STATE.GetBarrierInstance());
        }

        assert(ALL_REDUCE_GET_INSTANCE(recvBuf)  == GLOBAL_STATE.GetBarrierInstance());
        GLOBAL_STATE.barrierSkipCache[key] = ALL_REDUCE_GET_STATUS(recvBuf);

        if(ALL_REDUCE_GET_STATUS(recvBuf) == PARTICIPATE && ! gDisableAnalysis) {
            gAccessedRemoteData = false;
            Log(comm, key, "VetoOnFirstRound:", curBarrierInstance, gAccessedRemoteData);
        }
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
        // Clear the history in the hash table
        GLOBAL_STATE.barrierSkipCache.clear();
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

#ifdef ENABLE_REPLAY
    vector<char> replayLog;
    uint64_t replayIndex;
    void WriteToReplayLog(char replayVal){
        replayLog.push_back(replayVal);
    }
    
    void WriteReplayLogToFile(){
        FILE * replayFP = fopen("replay.txt", "w");
        assert(replayFP);
        for( int i = 0; i < replayLog.size(); i++) {
            char val = replayLog[i];
            fprintf(replayFP, "%c", val);
        }
        fclose(replayFP);
    }
    
    void ReadReplayLogToFile(){
        FILE * replayFP = fopen("replay.txt", "r");
        assert(replayFP);
        char val;
        while((val = fgetc(replayFP)) != EOF) {
            replayLog.push_back(val);
        }
        fclose(replayFP);
    }
    
    
    char GetReplayLogAtIndex(uint64_t index){
	if (index >= replayLog.size()) {
		printf("\n Replay log size is %d \n",replayLog.size()); 
	}
	assert(index < replayLog.size());
        return replayLog[index];
    }
#endif
    
    int WRAPPED_FUNCTION(MPI_Barrier)(MPI_Comm comm) {
        int retVal = MPI_SUCCESS;
        // increment the barrrier instance
        uint64_t curBarrierInstance = GLOBAL_STATE.IncrementBarrierInstance();

        // Not enabled, simple do the barrier and return
        if(!GLOBAL_STATE.IsEnabled()) {
            return REAL_FUNCTION(MPI_Barrier)(comm);
        }
        
        // Enabled, hence perform tracking / optimization

        
#ifdef ENABLE_REPLAY
        if (GLOBAL_STATE.GetReplayMode() == REPLAY_MODE_REPLAY){
            // If we are in reply mode, we will return from here.
            
            // Replay the result
            char replayVal = GetReplayLogAtIndex(replayIndex);
            replayIndex++;
            
            switch(replayVal) {
                case REPLAY_SKIP: {
                    // skip barrier
                    return MPI_SUCCESS;
                }
                default: {
                    // do barrier
                    return REAL_FUNCTION(MPI_Barrier)(comm);
                }
            }
        }
#endif

#ifdef VERBOSE
        uint64_t key = GetContextHashWithBackTrace();
#else
        uint64_t key = GetContextHash();
#endif
        // Is this barrier previously seen?
        GLOBAL_STATE.barrierSkipCacheIterator = GLOBAL_STATE.barrierSkipCache.find(key);

#ifdef ENABLE_REPLAY
        if(GLOBAL_STATE.GetReplayMode() == REPLAY_MODE_RECORD) {
            // Write to replay log
            // Anything other than "SKIP" is recorded as "PARTICIPATE"
            char replayVal;
            if(GLOBAL_STATE.barrierSkipCacheIterator != GLOBAL_STATE.barrierSkipCache.end()) {
                uint64_t val = GLOBAL_STATE.barrierSkipCacheIterator->second;
                switch(val) {
                    case SKIP: replayVal = REPLAY_SKIP; break;
                    default: replayVal = REPLAY_PARTICIPATE; break;
                }
            } else {
                replayVal = REPLAY_PARTICIPATE;
            }
            WriteToReplayLog(replayVal);
        }
#endif

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

    int WRAPPED_FUNCTION(MPI_Init)(int* argc, char** *argv) {
enable_barrier_optimization_();
        int retVal = REAL_FUNCTION(MPI_Init)(argc, argv);

        // make sure dense_hash_map is initialized with empty key
	GLOBAL_STATE.barrierSkipCache.set_empty_key(0);

        // Register my reduction op
        MPI_Op_create(MyMPIReductionOp, 1 /*commute*/, &myMPIOp);
        atexit(PrintStats);
        MPI_Comm_rank(MPI_COMM_WORLD, &myRank);


        // Get time after statring MPI
        if(myRank == 0) {
            gettimeofday(&mpiInitTime, NULL);
        }
        
#ifdef ENABLE_REPLAY
        char * val = getenv("NWCHEM_REPLAYMODE");
        if(val) {
            if (strcmp(val,"record") == 0 ) {
                GLOBAL_STATE.SetReplayMode(REPLAY_MODE_RECORD);
                // write the replay log to a file
                if(myRank == 0)
                    atexit(WriteReplayLogToFile);
            } else if (strcmp(val,"replay") == 0) {
                ReadReplayLogToFile();
                GLOBAL_STATE.SetReplayMode(REPLAY_MODE_REPLAY);
            } else {
                printf("\n Invalid NWCHEM_REPLAYMODE value %s", val);
                exit(-1);
            }
        }
#endif
        
#ifdef ENABLE_LOGGING
        CreateLogFile(myRank);
#ifdef VERBOSE

        // Register on exit function
        if(myRank == 0)
            atexit(DumpRedundancyMap);

#endif
        atexit(CloseLogFile);
#endif
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


