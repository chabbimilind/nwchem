set -ex
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-qsmp=omp -O3  -qinline  -DDOWORK -DTHE_WAIT=0 -DDOWORK_IN_CS"
CXX=xlc++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
mustBeAMultiple=1
throughput=512
timeout=60
nIter=99999999999990
level1TH=64
level2TH=64
level3TH=1
#$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt 
#$CXX $FLAGS -o hmcs_new_adapt hmcs_new_adapt.cpp -lrt
#$CXX $FLAGS -o hmcs_adapt_orig_c hmcs_adapt_orig.cpp  -lrt
#for mult in $(seq 1 128)
for DATA in 1 2 4 8 16 32 64 128 256 512 1024 2048
do
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_new_adapt hmcs_new_adapt.cpp -lrt
for mult in 1 2 4 8 16 32 64 128
do
#perf stat -e LLC-store-misses ./hmcs_ppc $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 2 32  $level2TH 128 $level3TH
./hmcs_ppc_latency $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
./hmcs_new_adapt $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
#./hmcs_adapt_orig_c $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
done
done
