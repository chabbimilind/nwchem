set -ex
S=/Users/mc29/softwares/Spin/Src6.4.2/
rm -f abort.pml.trail
rm -f pan.*
$S/spin  abort.pml
$S/spin  -a  abort.pml
#gcc -O3 -DVECTORSZ=2000 -DSAFETY -DCOLLAPSE  -o pan pan.c
gcc  -O3 -g  -DBITSTATE -DVECTORSZ=2000 -DSAFETY -o pan pan.c
#gcc -g -O3 -DVECTORSZ=53000 -DCOLLAPSE -DSAFETY -DMEMLIM=10000 -DNCORE=2 pan.c -o pan
./pan 
$S/spin -t  -l -p abort.pml
