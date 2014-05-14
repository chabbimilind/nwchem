set -ex
CFLAGS=-O3
CC -c -g $CFLAGS unwind_hash_time.cpp -I//global/u2/m/mc29/software/libunwind-1.1-install/include -fno-omit-frame-pointer
cd ~/nwchem-6.3_opt/src/
sh build_unwind_hash_time.sh
cd -
