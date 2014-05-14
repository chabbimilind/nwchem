set -ex
CFLAGS=-O0
CC -c -g $CFLAGS barrier_deletion.cpp -I//global/u2/m/mc29/software/libunwind-1.1-install/include -fno-omit-frame-pointer
#gcc -E -B -c test.c -o dmapp_wrapped.E -I/opt/cray/dmapp/7.0.1-1.0501.8315.8.4.ari/include  -I/opt/cray/gni-headers/3.0-1.0501.8317.12.1.ari/include
CC -E -B -c test.c -o dmapp_wrapped.E 
python dmapp-wrapper.py dmapp_wrapped.E  dmapp_wrapped.c  wrap_scrpt
CC -c -g $CFLAGS dmapp_wrapped.c -o dmapp_wrapped.o 
cd ~/nwchem-6.3_grace/src/
sh build_barrier_deletion.sh
cd -
