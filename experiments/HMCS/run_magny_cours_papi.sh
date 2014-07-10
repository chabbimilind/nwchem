set -ex
FLAGS="-fopenmp -g -O3 -I/projects/pkgs/papi-git/include/"
g++ $FLAGS -o hmcs_papi hmcs_papi.cpp -L/projects/pkgs/papi-git/lib/ -Wl,-rpath=/projects/pkgs/papi-git/lib/ -lpapi
export GOMP_CPU_AFFINITY="0-47"
throughput=64
nIter=9999999
time ./hmcs_papi $nIter 12 $throughput 2 12 12
time ./hmcs_papi $nIter 12 $throughput 3 6 12 12
