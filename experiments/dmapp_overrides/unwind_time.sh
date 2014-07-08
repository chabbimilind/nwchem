set -ex
CFLAGS=-O3
GOOGLE_SPARSE_HASH_PATH=/global/homes/m/mc29/experiments/sparsehash-2.0.2-install/
LIB_UNWIND_PATH=/global/u2/m/mc29/software/libunwind-1.1-install/
CC -c -g $CFLAGS unwind_time.cpp -I$GOOGLE_SPARSE_HASH_PATH/include -I$LIB_UNWIND_PATH/include -fno-omit-frame-pointer
cd ~/nwchem-6.3_opt/src/
sh build_unwind_time.sh
cd -
