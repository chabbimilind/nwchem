set -ex
FLAGS="-fopenmp -g -O3"
g++ $FLAGS -o hmcs hmcs.cpp
g++ $FLAGS -o mcs mcs.cpp
export GOMP_CPU_AFFINITY="0-47"
nIter=9999999
for i in 8 16 32 64 128 256 512 1024 2048 4096
do
./hmcs $nIter 12 $i 2 12 12
done
