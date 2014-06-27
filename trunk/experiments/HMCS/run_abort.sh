g++ -fopenmp -g -O3 -o mcs_abort mcs_abort.cpp
g++ -fopenmp -g -O3 -o mcs mcs.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=512
time ./mcs_abort 12 $throughput 2 12 12
#time ./mcs  12 $throughput 2 12 12
time ./mcs_abort 24 $throughput 2 12 24
#time ./mcs  24 $throughput 2 12 24
time ./mcs_abort 36 $throughput 2 12 36
#time ./mcs  36 $throughput 2 12 36
time ./mcs_abort 48 $throughput 2 12 48
#time ./mcs  48 $throughput 2 12 48
