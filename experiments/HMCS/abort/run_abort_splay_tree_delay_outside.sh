set -ex
# no -ex because MCS_abort or CLH_abort may crash
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-std=c++11 -fopenmp -Ofast  -mtune=native -march=native -g -DSPLAY_TREE_DRIVER -DPUFF"
#FLAGS="-std=c++11 -fopenmp -O0 -g"
CXX=g++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
mustBeAMultiple=1
throughput=512
timeout=60
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
nThreads=576
export OMP_NUM_THREADS=$nThreads
wokingThreads=576
prev=0
#myArray=0 100 500  1000  5000 10000  100000   1000000   10000000  100000000 1000000000
for wt in 0 100 500  1000  5000 10000  100000   1000000   10000000  100000000 1000000000
do
delta=$((wt-prev))
prev=$wt
$CXX $FLAGS -o hmcs_abort hmcs_abort.cpp -lrt  -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
$CXX $FLAGS -o TATAS TATAS.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
$CXX $FLAGS -o CLH_abort CLH_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
$CXX $FLAGS -o CLH_NB_abort CLH_NB_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -ltcmalloc -DDELTA_SLEEP=$delta
$CXX $FLAGS -o MCS_abort MCS_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
$CXX $FLAGS -o MCS_NB_abort MCS_NB_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -ltcmalloc -DDELTA_SLEEP=$delta
$CXX $FLAGS -o A_BO_CLH_NB_abort A_BO_CLH_NB_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -ltcmalloc -DDELTA_SLEEP=$delta
$CXX $FLAGS -o A_BO_HMCS_abort A_BO_HMCS_abort.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta 
for waitThreshold in 0  1000  10000  100000   1000000   1000000000000
do
mult=1
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 72 $level3TH  $nThreads $level4TH
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 36 $level3TH  $nThreads $level4TH
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads  3 36 $level2TH 72 $level3TH $nThreads $level3TH
numactl --localalloc ./hmcs_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads  4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
numactl --localalloc ./TATAS $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
./MCS_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH || echo "CRASHED"
./CLH_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
./MCS_NB_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
./CLH_NB_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
numactl --localalloc ./A_BO_CLH_NB_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 36 $level2TH $nThreads $level4TH
numactl --localalloc ./A_BO_HMCS_abort $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 36 $level2TH $nThreads $level4TH
done
done

######## Non abort
waitThreshold=1000000000000
mult=1
prev=0
for wt in 0 100 500  1000  5000 10000  100000   1000000   10000000  100000000 1000000000
do
delta=$((wt-prev))
prev=$wt
$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp -lrt   -DDOWORK -DMAX_DATA=2 -DMIN_SLEEP=$wt -DDELTA_SLEEP=$delta
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 1 $nThreads $level4TH
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 72 $level3TH  $nThreads $level4TH
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 2 36 $level3TH  $nThreads $level4TH
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 3 36 $level2TH 72 $level3TH $nThreads $level3TH
numactl --localalloc ./hmcs_ppc_latency $mult $timeout $nIter $waitThreshold $nThreads $wokingThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
done
