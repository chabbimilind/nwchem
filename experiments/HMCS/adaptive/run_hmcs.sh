set -ex
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-qsmp=omp -O3  -qinline -DDOWORK -DDOWORK_IN_CS -DTHE_WAIT=0"
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
#time ./hmcs_ppc $timeout $nIter 12 3 6 $level1TH 12  $level2TH 12 $level3TH
#time ./hmcs_ppc $timeout $nIter 24 3 6 $level1TH 12  $level2TH 24 $level3TH
#time ./hmcs_ppc $timeout $nIter 36 3 6 $level1TH 12  $level2TH 36 $level3TH
#time ./hmcs_ppc $timeout $nIter 48 3 6 $level1TH 12  $level2TH 48 $level3TH
#for i in 0 100 500 700 800 900 1000 1100 1200 1300 1400 1500 1600 1700 1800 1900 2000 2100 2200 2300 2400 2500 2700 3000 4000 5000 5100 5200 5300 5400 5500 5600 5700 5800 5900 6000 6100 6200 6300 6400 6500 6700 7000 7200 7500 8000 9000 10000
$CXX $FLAGS -o hmcs_ppc hmcs_ppc.cpp -lrt 
$CXX $FLAGS -o hmcs_ppc_adapt_c hmcs_adapt.cpp -lrt
#$CXX $FLAGS -o hmcs_adapt_orig_c hmcs_adapt_orig.cpp  -lrt
#for mult in $(seq 1 128)
for mult in 1 2 4 8 16 32 64 128
do
#perf stat -e LLC-store-misses ./hmcs_ppc $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc $mult $timeout $nIter 128 1 128 $level3TH
./hmcs_ppc $mult $timeout $nIter 128 2 32  $level2TH 128 $level3TH
./hmcs_ppc $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
./hmcs_ppc_adapt_c $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
#./hmcs_adapt_orig_c $mult $timeout $nIter 128 3 4 $level1TH 32  $level2TH 128 $level3TH
done
