set -ex
S=/mnt/fileserver-5/a/users/mc29/software/machines/dl580/Spin/Src6.4.4/
F=$1
rm -f ${F}.trail
rm -f pan.*
#$S/spin  abort.pml
$S/spin -a  ${F}
#icc -w -O3 -DVECTORSZ=53000 -DCOLLAPSE -DSAFETY -DMEMLIM=2000 -DNCORE=16 pan.c -o phaser_f_16
#gcc -O3 -DVECTORSZ=2400 -DSAFETY -DCOLLAPSE  -DMEMLIM=236000 -DNCORE=32 -o pan pan.c
#gcc -O3  -DVECTORSZ=2400 -DSAFETY -DCOLLAPSE  -DMEMLIM=251000 -DNCORE=1 -o ${F}.pan pan.c
#gcc -O3 -DVECTORSZ=2000 -DCOLLAPSE -DSAFETY -DMEMLIM=950000 -DNCORE=8   pan.c  -o ${F}.pan
#gcc -Wfatal-errors -O3 -DNOBOUNDCHECK -DVECTORSZ=400 -DCOLLAPSE -DSAFETY    -DNCORE=144 pan.c  -o ${F}.pan -DMEMLIM=23068672 
#gcc -Wfatal-errors -O3 -DNOBOUNDCHECK -DVECTORSZ=400 -DCOLLAPSE -DSAFETY    -DNCORE=16 pan.c  -o ${F}.pan -DSFH -DMEMLIM=1000000
#gcc  -O3 -DBITSTATE -DVECTORSZ=9999 -DSAFETY -o pan pan.c
#taskset -c 0-17 ./${F}.pan
#time sudo ./${F}.pan
gcc -Wfatal-errors -O3 -DNOBOUNDCHECK -DVECTORSZ=400 -DCOLLAPSE -DSAFETY    -DNCORE=1 pan.c  -o ${F}.pan -DSFH -DMEMLIM=23068672 -DUSE_HUGE_PAGE
time sudo ./${F}.pan
#sudo numactl --localalloc ./${F}.pan
$S/spin -t  -l -p ${F}
