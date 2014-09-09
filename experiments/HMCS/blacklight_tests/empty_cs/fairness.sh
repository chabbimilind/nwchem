set -ex
#FLAGS="-g -fast -openmp -ipo -xhost"
FLAGS=" -fast -openmp -ipo -xhost"
LIBS=" -lrt "
CXX=icc
$CXX $FLAGS -o hmcs_blacklight hmcs_ppc.cpp $LIBS
#export KMP_AFFINITY=verbose,granularity=fine,compact
#explicitly set PBS env
export PBS_HT_NCPUS=4096
export KMP_AFFINITY=granularity=fine,compact
export OMP_NUM_THREADS=$PBS_HT_NCPUS
export OMP_WAIT_POLICY=active
echo $OMP_NUM_THREADS
echo $PBS_HT_NCPUS
#cat /dev/cpuset/torque/${PBS_JOBID}/cpus
timeout=300
infL=9223372036854775807
inf=2147483647
totalThreads=$OMP_NUM_THREADS

echo "C-MCS inner cohort"
nIter=$infL
numLevels=2
k1=2
n1=2
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n1 $k1  $totalThreads $inf

echo "C-MCS middle cohort"
nIter=$infL
numLevels=2
km=16
nm=16
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $nm $km $totalThreads $inf

echo "C-MCS outer cohort"
nIter=$infL
numLevels=2
k2=512
n2=512
time ./hmcs_blacklight $timeout $nIter  $totalThreads $numLevels $n2 $k2 $totalThreads $inf

echo "HMCS 6 level"
nIter=$infL
numLevels=6
n1=2
t1=2
n2=16
t2=8
n3=32
t3=2
n4=64
t4=2
n5=512
t5=8
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n1 $t1 $n2 $t2 $n3 $t3 $n4 $t4 $n5 $t5 $n6 $t6

echo "HMCS 5 level"
nIter=$infL
numLevels=5
n12=16
t12=16
n3=32
t3=2
n4=64
t4=2
n5=512
t5=8
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n12 $t12 $n3 $t3 $n4 $t4 $n5 $t5 $n6 $t6

echo "HMCS 4 level"
nIter=$infL
numLevels=4
n123=32
t123=32
n4=64
t4=2
n5=512
t5=8
n6=4096
t6=$inf
time ./hmcs_blacklight $timeout $nIter $totalThreads $numLevels $n123 $t123 $n4 $t4 $n5 $t5 $n6 $t6
