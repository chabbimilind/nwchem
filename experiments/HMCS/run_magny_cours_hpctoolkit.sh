set -ex
FLAGS="-fopenmp -g -O3"
g++ $FLAGS -o hmcs hmcs.cpp
g++ $FLAGS -o mcs mcs.cpp
export GOMP_CPU_AFFINITY="0-47"
throughput=64
throughput_2_level=4096
nIter=99999990
H=/projects/hpc/mc29/HPCToolkit/hpctoolkit-install/bin
rm -rf measure_3_level measure_2_level db_2_3_level  db_2_level measure_2_level db_3_level measure_3_level
#L3_CACHE_MISSES:ANY_READ@50000 
#$H/hpcrun -e HYPERTRANSPORT_LINK0:ALL@5000000 -e HYPERTRANSPORT_LINK1:ALL@500 -e HYPERTRANSPORT_LINK2:ALL@500 -e HYPERTRANSPORT_LINK3:ALL@500 -o measure_2_level ./hmcs $nIter 48 $throughput_2_level 2 12 48
#$H/hpcrun -e HYPERTRANSPORT_LINK0:ALL@5000000 -e HYPERTRANSPORT_LINK1:ALL@500 -e HYPERTRANSPORT_LINK2:ALL@500 -e HYPERTRANSPORT_LINK3:ALL@500 -o measure_3_level ./hmcs $nIter 48 $throughput 3 6 12 48
$H/hpcrun -e PAPI_TOT_CYC@5000000 -e HYPERTRANSPORT_LINK0:ALL@5000000 -o measure_2_level ./hmcs $nIter 48 $throughput_2_level 2 12 48
$H/hpcrun -e PAPI_TOT_CYC@5000000 -e HYPERTRANSPORT_LINK0:ALL@5000000 -o measure_3_level ./hmcs $nIter 48 $throughput 3 6 12 48
$H/hpcstruct ./hmcs
$H/hpcprof -S hmcs.hpcstruct -o db_2_3_level measure_2_level measure_3_level
