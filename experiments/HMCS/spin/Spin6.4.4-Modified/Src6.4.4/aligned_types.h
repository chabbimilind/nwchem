#ifndef __ALIGNED_TYPES__
#define __ALIGNED_TYPES__
       #ifndef CACHE_LINE_SZ
       #define CACHE_LINE_SZ  (128)
       #endif
        typedef union AlignedInt{volatile int i; char pad[CACHE_LINE_SZ];} AlignedInt_t;
        typedef union AlignedDouble{volatile double d;char pad[CACHE_LINE_SZ];} AlignedDouble_t;
        typedef union AlignedLong{volatile long l;char pad[CACHE_LINE_SZ];} AlignedLong_t;
        typedef union AlignedULong{volatile unsigned long ul;char pad[CACHE_LINE_SZ];} AlignedULong_t;
        typedef union AlignedUInt{volatile unsigned int  ui;char pad[CACHE_LINE_SZ];} AlignedInt_t;
#endif

