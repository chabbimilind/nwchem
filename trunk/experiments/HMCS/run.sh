set -ex
FLAGS="-fopenmp -g -O3"
g++ $FLAGS -o hmcs hmcs.cpp
g++ $FLAGS -o hand_unrolled_hmcs hand_unrolled_hmcs.cpp
g++ $FLAGS -o mcs mcs.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=512
nIter=9999999
time ./hmcs $nIter 12 $throughput 2 12 12
time ./hand_unrolled_hmcs $nIter 12 $throughput 2 12 12
time ./mcs  $nIter 12 
time ./hmcs $nIter 24 $throughput 2 12 24
time ./hand_unrolled_hmcs $nIter 24 $throughput 2 12 24
time ./mcs  $nIter 24 
time ./hmcs $nIter 36 $throughput 2 12 36
time ./hand_unrolled_hmcs $nIter 36 $throughput 2 12 36
time ./mcs  $nIter 36 
time ./hmcs $nIter 48 $throughput 2 12 48
time ./hand_unrolled_hmcs $nIter 48 $throughput 2 12 48
time ./mcs  $nIter 48 
