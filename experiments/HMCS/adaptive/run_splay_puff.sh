set -ex
#FLAGS="-qsmp=omp -O3  -qinline"
#FLAGS="-qsmp=omp -g -O0  -qinline"
FLAGS="-fopenmp -Ofast  -mtune=native -march=native -g"
CXX=g++
#$CXX $FLAGS -o hmcs_ppc_adapt hmcs_adapt.cpp -lrt
#export GOMP_CPU_AFFINITY="0-47"
mustBeAMultiple=1
throughput=512
timeout=30
nIter=99999999999990
level1TH=64
level2TH=64
level3TH=64
level4TH=1
#$CXX $FLAGS -o hmcs_ppc_latency hmcs_ppc_latency.cpp  -lrt 
#$CXX $FLAGS -o hmcs_new_adapt hmcs_new_adapt.cpp -lrt
#$CXX $FLAGS -o hmcs_adapt_orig_c hmcs_adapt_orig.cpp  -lrt
#for mult in $(seq 1 128)
#for DATA in 1 2 4 8 16 32 64 128 256 512 1024 2048
$CXX $FLAGS -o hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE.cpp -lrt 
$CXX $FLAGS -o hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE_tsx hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE.cpp -lrt -DUSE_TSX
$CXX $FLAGS -o hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE_tsx_avoid_lemming hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE.cpp -lrt -DUSE_TSX -DAVOID_LEMMING_EFFECT
$CXX $FLAGS -o hmcs_ppc_latency_SPLAY_TREE hmcs_ppc_latency_SPLAY_TREE.cpp -lrt 
nThreads=576
export OMP_NUM_THREADS=$nThreads
#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_ppc_latency_SPLAY_TREE $mult $timeout $nIter $nThreads 1 $nThreads $level4TH
#done
#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_ppc_latency_SPLAY_TREE $mult $timeout $nIter $nThreads 2 72 $level3TH  $nThreads $level4TH
#done
#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_ppc_latency_SPLAY_TREE $mult $timeout $nIter $nThreads 3 36 $level2TH 72 $level3TH $nThreads $level3TH
#done
#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_ppc_latency_SPLAY_TREE $mult $timeout $nIter $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
#done
#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE $mult $timeout $nIter $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
#done

#for mult in 576 288 144 72 36 18 9 6 3 1
#do
#./hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE_tsx $mult $timeout $nIter $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
#done

for mult in 576 288 144 72 36 18 9 6 3 1
do
./hmcs_adapt_instantaneous_slow_fast_reuse_next_SPLAY_TREE_tsx_avoid_lemming $mult $timeout $nIter $nThreads 4 2 $level1TH  36 $level2TH 72 $level3TH $nThreads $level4TH
done
