set -ex
CFLAGS=-O3
CC -c -g $CFLAGS timing.cpp 
cd ~/nwchem-6.3_opt/src/
sh build_timing.sh
cd -
