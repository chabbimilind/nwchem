set -ex
###FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -O3  -qinline -DDOWORK -DDOWORK_IN_CS  -DMAX_DATA=4"
FLAGS="-qsmp=omp -O3  -qinline -DDOWORK -DDOWORK_IN_CS"
CXX=xlc++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
#export OMP_WAIT_POLICY=PASSIVE
export OMP_WAIT_POLICY=ACTIVE
mustBeAMultiple=1
throughput=512
timeout=5
nIter=9999999990
level1TH=64
level2TH=64
level3TH=1
#time ./hmcs_ppc $timeout $nIter 12 3 6 $level1TH 12  $level2TH 12 $level3TH
#time ./hmcs_ppc $timeout $nIter 24 3 6 $level1TH 12  $level2TH 24 $level3TH
#time ./hmcs_ppc $timeout $nIter 36 3 6 $level1TH 12  $level2TH 36 $level3TH
#time ./hmcs_ppc $timeout $nIter 48 3 6 $level1TH 12  $level2TH 48 $level3TH
#for i in 0 100 500 700 800 900 1000 1100 1200 1300 1400 1500 1600 1700 1800 1900 2000 2100 2200 2300 2400 2500 2700 3000 4000 5000 5100 5200 5300 5400 5500 5600 5700 5800 5900 6000 6100 6200 6300 6400 6500 6700 7000 7200 7500 8000 9000 10000
#for i in 2 4
for i in 4 
do
#for j in 1 10 100
for j in 1
do
$CXX -DHOW_LONG_MS=$j -DMAX_DATA=$i -DNITER=4 $FLAGS -DTHE_WAIT="0" -o hmcs_ppc hmcs_ppc_latency.cpp -lrt  &
$CXX -DHOW_LONG_MS=$j -DMAX_DATA=$i -DNITER=4 $FLAGS -DTHE_WAIT="0" -o hmcs_adapt_counter_based hmcs_adapt_counter_based.cpp -lrt  &
$CXX -DHOW_LONG_MS=$j -DMAX_DATA=$i -DNITER=4 $FLAGS -DTHE_WAIT="0" -o hmcs_adapt_instantaneous_slow_fast_reuse_next hmcs_adapt_instantaneous_slow_fast_reuse_next.cpp -lrt  &
wait 
time ./hmcs_ppc $mustBeAMultiple $timeout $nIter 128 1 128 $level3TH
time ./hmcs_ppc $mustBeAMultiple $timeout $nIter 128 2 32  $level2TH 128 $level3TH
time ./hmcs_ppc $mustBeAMultiple $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
time ./hmcs_adapt_counter_based $mustBeAMultiple $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
time ./hmcs_adapt_instantaneous_slow_fast_reuse_next $mustBeAMultiple $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
done
done
