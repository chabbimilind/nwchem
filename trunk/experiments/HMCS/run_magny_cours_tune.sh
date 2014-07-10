set -ex
FLAGS="-fopenmp -g -O0"
g++ $FLAGS -o hmcs_tune hmcs_tune.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=512
nIter=9999999
level3TH=1
for level2TH in 1 2 4 8 16 32 64 128 256 512 1024 2048 4096
do
for level1TH in 1 2 4  8 16 32 64 128 256 512 1024 2048 4096
do
time ./hmcs_tune $nIter 48 3 6 $level1TH 12  $level2TH 48 $level3TH
done
done
