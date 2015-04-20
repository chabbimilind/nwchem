set -ex
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-qsmp=omp -O3  -qinline"
CXX=xlc++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
mustBeAMultiple=1
throughput=512
timeout=30
nIter=99999999999990
level1TH=64
level2TH=64
level3TH=1
$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt 
$CXX $FLAGS -o hmcs_ppc_latency_slow_fast hmcs_ppc_latency_slow_fast.cpp -lrt
#$CXX $FLAGS -o hmcs_adapt_orig_c hmcs_adapt_orig.cpp  -lrt
#for mult in $(seq 1 128)
for mult in 1 2 4 8 16 32 64 128
do
#perf stat -e LLC-store-misses ./hmcs_ppc $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 2 32  $level2TH 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
./hmcs_ppc_latency_slow_fast  $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
#./hmcs_adapt_orig_c $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
done
