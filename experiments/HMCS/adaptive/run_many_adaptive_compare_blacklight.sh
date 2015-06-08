set -ex
FLAGS=" -fast -openmp -ipo -xhost -DDOWORK -DTHE_WAIT=0 -DDOWORK_IN_CS -DBLACKLIGHT"
LIBS=" -lrt "
CXX=icc
#export KMP_AFFINITY=verbose,granularity=fine,compact
export KMP_AFFINITY=granularity=fine,compact
export OMP_NUM_THREADS=$PBS_HT_NCPUS
export OMP_WAIT_POLICY=active
echo $OMP_NUM_THREADS
echo $PBS_HT_NCPUS
mustBeAMultiple=1
throughput=512
timeout=30
nIter=99999999999990
level1TH=64
level2TH=64
level3TH=64
level4TH=1
for DATA in 0 1 2 4 8 16 32 64 128  256 512 1024 
do
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_adapt_check_root_first hmcs_new_adapt.cpp -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_new_adapt_check_cur_first  hmcs_new_adapt_check_cur_first.cpp -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_adapt_counter_based_atomic hmcs_adapt_counter_based.cpp -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_adapt_counter_based_non_atomic hmcs_adapt_counter_based_non_atomic.cpp -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_adapt_counter_based_atomic_check_cur_first hmcs_adapt_counter_based_check_cur_first.cpp -lrt &
$CXX $FLAGS -DMAX_DATA=${DATA} -o hmcs_adapt_counter_based_non_atomic_check_cur_first hmcs_adapt_counter_based_non_atomic_check_cur_first.cpp -lrt &
wait
for mult in 1 2 4 8 16 32 64 128 256
do
./hmcs_ppc_latency $mult $timeout $nIter 256 1 256 $level4TH
./hmcs_ppc_latency $mult $timeout $nIter 256 2 64  $level3TH 256 $level4TH
./hmcs_ppc_latency $mult $timeout $nIter 256 3 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_ppc_latency $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_adapt_check_root_first $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_new_adapt_check_cur_first $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_adapt_counter_based_atomic $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_adapt_counter_based_non_atomic $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_adapt_counter_based_atomic_check_cur_first $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
./hmcs_adapt_counter_based_non_atomic_check_cur_first $mult $timeout $nIter 256 4 2 $level1TH 16 $level2TH 64  $level3TH 256 $level4TH
done
done
