set -ex
CFLAGS=-O3
CC -c -g wait_times.cpp $CFLAGS 
cd ~/nwchem-6.3_opt/src/
sh build_wait_times.sh
cd -
