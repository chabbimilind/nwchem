set -ex
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-std=c++11 -fopenmp -Ofast  -mtune=native -march=native -g"
#FLAGS="-std=c++11 -fopenmp -O0 -g"
CXX=g++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
mustBeAMultiple=1
throughput=512
timeout=30
nIter=99999999999990
#waitThreshold=99999999999990
level1TH=64
level2TH=64
level3TH=64
level4TH=1
#$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt 
#$CXX $FLAGS -o hmcs_new_adapt hmcs_new_adapt.cpp -lrt
#$CXX $FLAGS -o hmcs_adapt_orig_c hmcs_adapt_orig.cpp  -lrt
#for mult in $(seq 1 128)
#for DATA in 1 2 4 8 16 32 64 128 256 512 1024 2048
$CXX $FLAGS -o hmcs_abort hmcs_abort.cpp -lrt  -DDOWORK -DMAX_DATA=2 -DTHE_WAIT=0 
$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DTHE_WAIT=0
$CXX $FLAGS -o TATAS TATAS.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DTHE_WAIT=0
nThreads=576

export OMP_NUM_THREADS=$nThreads

##### TATAS

for waitThreshold in 0 100 500 1000 10000 1000000 100000000 10000000000 1000000000000
do
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./TATAS $mult $timeout $nIter $waitThreshold $nThreads 1 $nThreads $level4TH
done
done



exit


###### abort

for waitThreshold in 0 100 500 1000 10000 1000000 100000000 10000000000 1000000000000
do
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads 1 $nThreads $level4TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads 2 72 $level3TH  $nThreads $level4TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads 3 36 $level2TH 72 $level3TH $nThreads $level3TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
done
done

exit 

######## Non abort
waitThreshold=1000000000000
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads 1 $nThreads $level4TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads 2 72 $level3TH  $nThreads $level4TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads 3 36 $level2TH 72 $level3TH $nThreads $level3TH
done
for mult in 576 288 144 72 36 18 9 6 3 1
do
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
done
