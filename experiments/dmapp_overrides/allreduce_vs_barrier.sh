set -ex
CFLAGS=-O3
CC -c -g $CFLAGS allreduce_time.cpp 
cd ~/nwchem-6.3_opt/src/
sh build_allreduce_time.sh
cd -
