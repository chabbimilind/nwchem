set -ex
FLAGS="-fopenmp -g -O3"
g++ $FLAGS -o hmcs_ppc hmcs_ppc.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=512
nIter=99999990
level1TH=64
level2TH=64
level3TH=1
time ./hmcs_ppc $nIter 12 3 6 $level1TH 12  $level2TH 12 $level3TH
time ./hmcs_ppc $nIter 24 3 6 $level1TH 12  $level2TH 24 $level3TH
time ./hmcs_ppc $nIter 36 3 6 $level1TH 12  $level2TH 36 $level3TH
time ./hmcs_ppc $nIter 48 3 6 $level1TH 12  $level2TH 48 $level3TH
