#ifndef __ALIGNED_TYPES__
#define __ALIGNED_TYPES__
       #ifndef CACHE_LINE_SZ
       #define CACHE_LINE_SZ  (128)
       #endif
        typedef struct AlignedInt{struct {char pad[CACHE_LINE_SZ]; volatile int i;}; char pad1[CACHE_LINE_SZ];} AlignedInt_t;
        typedef struct AlignedDouble{struct {char pad[CACHE_LINE_SZ]; volatile double d; };char pad1[CACHE_LINE_SZ];} AlignedDouble_t;
        typedef struct AlignedLong{struct {char pad[CACHE_LINE_SZ]; volatile long l;}; char pad1[CACHE_LINE_SZ];} AlignedLong_t;
        typedef struct AlignedULong{struct {char pad[CACHE_LINE_SZ]; volatile unsigned long ul;}; char pad1[CACHE_LINE_SZ];} AlignedULong_t;
        typedef struct AlignedUInt{struct {char pad[CACHE_LINE_SZ]; volatile unsigned int  ui; };char pad1[CACHE_LINE_SZ];} AlignedUInt_t;
#endif

