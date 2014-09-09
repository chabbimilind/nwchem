#!/bin/bash
set -ex
FLAGS="-fast -openmp -ipo -xhost"
#FLAGS="-g -O0 -fopenmp "
LIBS=" -lrt "
CXX=icc
#$CXX $FLAGS -o hmcs_blacklight hmcs_ppc.cpp $LIBS
#export KMP_AFFINITY=verbose,granularity=fine,compact
export KMP_AFFINITY=granularity=fine,compact
#explicitly set PBS env
export PBS_HT_NCPUS=4096
export OMP_NUM_THREADS=$PBS_HT_NCPUS
export OMP_WAIT_POLICY=active
echo $OMP_NUM_THREADS
echo $PBS_HT_NCPUS
#cat /dev/cpuset/torque/${PBS_JOBID}/cpus
#time out in 10 mins
timeout=600
infL=9223372036854775807
inf=2147483647
totalThreads=$OMP_NUM_THREADS

echo "C-MCS inner cohort"
#5K per thread should take about 3 min
nIter=$((50000 * totalThreads))
numLevels=2
k1=$inf
n1=2
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n1 $k1  $totalThreads $inf

echo "C-MCS middle cohort"
#3K per thread should take about 3 min
nIter=$((50000 * totalThreads))
numLevels=2
km=$inf
nm=16
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $nm $km $totalThreads $inf

echo "C-MCS outer cohort"
#2K per thread should take about 8 mins
nIter=$((20000 * totalThreads))
numLevels=2
k2=$inf
n2=512
time ./hmcs_blacklight $timeout $nIter  $totalThreads $numLevels $n2 $k2 $totalThreads $inf

echo "HMCS 6 level"
# 25 per thread should take about 60 sec
nIter=$((250000 * totalThreads))
numLevels=6
n1=2
t1=$inf
n2=16
t2=$inf
n3=32
t3=$inf
n4=64
t4=$inf
n5=512
t5=$inf
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n1 $t1 $n2 $t2 $n3 $t3 $n4 $t4 $n5 $t5 $n6 $t6

echo "HMCS 5 level"
#3K per thread will take about 3 mins
nIter=$((50000 * totalThreads))
numLevels=5
n12=16
t12=$inf
n3=32
t3=$inf
n4=64
t4=$inf
n5=512
t5=$inf
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n12 $t12 $n3 $t3 $n4 $t4 $n5 $t5 $n6 $t6

echo "HMCS 4 level"
# 2K per thread should talke about 4 mins
nIter=$((20000 * totalThreads))
numLevels=4
n123=32
t123=$inf
n4=64
t4=$inf
n5=512
t5=$inf
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n123 $t123 $n4 $t4 $n5 $t5 $n6 $t6
