set -ex
FLAGS="-fopenmp -g -O3"
g++ $FLAGS -DTEST_TRY_RELEASE -o hmcs_no_try_release hmcs_phase.cpp
g++ $FLAGS -o hmcs_try_release hmcs_phase.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=16
throughput_2_level=64
nIter=99999990
time ./hmcs_no_try_release $nIter 12 $throughput 3 6 12 12
time ./hmcs_try_release $nIter 12 $throughput 3 6 12 12
time ./hmcs_no_try_release $nIter 24 $throughput 3 6 12 24
time ./hmcs_try_release $nIter 24 $throughput 3 6 12 24
time ./hmcs_no_try_release $nIter 36 $throughput 3 6 12 36
time ./hmcs_try_release $nIter 36 $throughput 3 6 12 36
time ./hmcs_no_try_release $nIter 48 $throughput 3 6 12 48
time ./hmcs_try_release $nIter 48 $throughput 3 6 12 48
