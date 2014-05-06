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
#include<dmapp.h>
#include<mpi.h>
#include<sys/time.h>


using namespace std;
using namespace std::tr1;

extern "C" {

#define TIME_SPENT(start, end) (end.tv_sec * 1000000 + end.tv_usec - start.tv_sec*1000000 - start.tv_usec)
#define TIME_USEC(t) (t.tv_sec * 1000000 + t.tv_usec)

    
#define REAL_FUNCTION(name)  __real_ ## name
#define WRAPPED_FUNCTION(name)  __wrap_ ## name
    
    
    /******** Globals variables **********/
    
    struct timeval acquireStart;
    struct timeval acquireEnd;

    struct timeval releaseStart;
    struct timeval releaseEnd;

    
    int WRAPPED_FUNCTION(MPI_Initialize) (){
                atexit(OnEnd);
        
        int retVal = MPI_SUCCESS;
        return retVal;
        
    }
    
    
    extern dmapp_return_t
    REAL_FUNCTION(dmapp_lock_acquire) ( dmapp_lock_desc_t *lock_addr,
                                       dmapp_seg_desc_t *lock_seg,
                                       dmapp_pe_t lock_host,
                                       uint64_t flags,
                                       dmapp_lock_handle_t *handle) ;
    dmapp_return_t
    WRAPPED_FUNCTION(dmapp_lock_acquire) ( dmapp_lock_desc_t *lock_addr,
                                          dmapp_seg_desc_t *lock_seg,
                                          dmapp_pe_t lock_host,
                                          uint64_t flags,
                                          dmapp_lock_handle_t *handle) {
        
        
        gettimeofday(&acquireStart, 0);
        dmapp_return_t val = REAL_FUNCTION(dmapp_lock_acquire)(lock_addr, lock_seg, lock_host, flags, handle);
        gettimeofday(&acquireEnd, 0);
        // Log to buffer
        uint64_t acquireTime = TIME_SPENT(acquireStart, acquireEnd);
        LogToBuffer(TIME_USEC(acquireStart), acquireTime);

        return val;
        
    }
    
    extern dmapp_return_t
    REAL_FUNCTION(dmapp_lock_release) ( dmapp_lock_handle_t handle,
                                       uint64_t flags) ;
    dmapp_return_t
    WRAPPED_FUNCTION(dmapp_lock_release) ( dmapp_lock_handle_t handle, uint64_t flags) {
        gettimeofday(&releaseStart, 0);
        dmapp_return_t val = REAL_FUNCTION(dmapp_lock_release)(handle, flags);
        gettimeofday(&releaseEnd, 0);

        uint64_t csTime = TIME_SPENT(acquireEnd, releaseStart);
        uint64_t releaseTime = TIME_SPENT(releaseStart, releaseEnd);
        
        LogToBuffer(acquireTime, csTime, releaseTime);
        
        return val;
    }

    
}


