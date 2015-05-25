set -ex
###FLAGS="-qsmp=omp -O3  -qinline"
FLAGS="-qsmp=omp -O3  -qinline -DDOWORK -DDOWORK_IN_CS -DDOWORK_OUTSIDE_CS -DPROFILE -DMAX_DATA=2"
CXX=xlc++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
#export OMP_WAIT_POLICY=PASSIVE
mustBeAMultiple=1
throughput=512
timeout=20
nIter=9999999990
level1TH=64
level2TH=64
level3TH=1
#time ./hmcs_ppc $timeout $nIter 12 3 6 $level1TH 12  $level2TH 12 $level3TH
#time ./hmcs_ppc $timeout $nIter 24 3 6 $level1TH 12  $level2TH 24 $level3TH
#time ./hmcs_ppc $timeout $nIter 36 3 6 $level1TH 12  $level2TH 36 $level3TH
#time ./hmcs_ppc $timeout $nIter 48 3 6 $level1TH 12  $level2TH 48 $level3TH
#for i in 0 100 500 700 800 900 1000 1100 1200 1300 1400 1500 1600 1700 1800 1900 2000 2100 2200 2300 2400 2500 2700 3000 4000 5000 5100 5200 5300 5400 5500 5600 5700 5800 5900 6000 6100 6200 6300 6400 6500 6700 7000 7200 7500 8000 9000 10000
for i in $(seq 1200 300 12000)
do
$CXX $FLAGS -DTHE_WAIT="$i" -o hmcs_adapt_instantaneous_slow_fast hmcs_adapt_instantaneous_slow_fast.cpp -lrt 
time ./hmcs_adapt_instantaneous_slow_fast $mustBeAMultiple $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
done
