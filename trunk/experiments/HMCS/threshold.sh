export GOMP_CPU_AFFINITY="0-47"
for i in 1 2 4 8 16 32 64 128 256 512 1024 2048 4096
do
time ./hmcs 48 $i 2 12 48
done
