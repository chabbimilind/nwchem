set -ex
export NWCHEM_TOP=/global/homes/m/mc29/nwchem-6.3_opt/
export NWCHEM_TARGET=LINUX64
export NWCHEM_MODULES=all
export USE_MPI=y
export USE_MPIF=y
export USE_MPIF4=y
export USE_SCALAPACK=y
export USE_64TO32=y
export LIBMPI=" "
module swap PrgEnv-intel PrgEnv-gnu
module load craype-hugepages64M
#module load gcc/4.7.2  
export ARMCI_NETWORK=DMAPP
export USE_SCALAPACK=y
export SCALAPACK=-lsci_gnu
export SCALAPACK_LIB=-lsci_gnu
export BLASOPT=-lsci_gnu
export BLAS_LIB=-lsci_gnu
export LAPACK_LIB=-lsci_gnu
export USE_64TO32=y
export CFLAGS_FORGA="-g -fno-omit-frame-pointer"
make nwchem_config 
make realclean
make 64_to_32 
#make FC=/global/homes/m/mc29/myCompilerWrapper/myFC.sh CC=/global/homes/m/mc29/myCompilerWrappers/myCC.sh   >& make.log
make FC=ftn FDEBUG="-g -fno-omit-frame-pointer" CDEBUG="-g -fno-omit-frame-pointer" >& make.log
#ftn -fdefault-integer-8 -Wextra -Wuninitialized  -g -O   -I.  -I/global/homes/m/mc29/nwchem-6.3_opt//src/include -I/global/homes/m/mc29/nwchem-6.3_opt//src/tools/install/include -DCRAYXT -DEAFHACK -DNOFSCHECK -DEXT_INT -DLINUX -DLINUX64 -DCHKUNDFLW -DGCC4 -DGCC46 -DSCALAPACK -DPARALLEL_DIAG -DCOMPILATION_DATE="'`date +%a_%b_%d_%H:%M:%S_%Y`'" -DCOMPILATION_DIR="'/global/homes/m/mc29/nwchem-6.3_opt/'" -DNWCHEM_BRANCH="'6.3'"  -c -o nwchem.o nwchem.F
#ftn -fdefault-integer-8 -Wextra -Wuninitialized  -g -O   -I.  -I/global/homes/m/mc29/nwchem-6.3_opt//src/include -I/global/homes/m/mc29/nwchem-6.3_opt//src/tools/install/include -DCRAYXT -DEAFHACK -DNOFSCHECK -DEXT_INT -DLINUX -DLINUX64 -DCHKUNDFLW -DGCC4 -DGCC46 -DSCALAPACK -DPARALLEL_DIAG -DCOMPILATION_DATE="'`date +%a_%b_%d_%H:%M:%S_%Y`'" -DCOMPILATION_DIR="'/global/homes/m/mc29/nwchem-6.3_opt/'" -DNWCHEM_BRANCH="'6.3'"  -c -o stubs.o stubs.F
#/global/homes/m/mc29/software/hpctoolkit/hpctoolkit-install/bin/hpclink ftn   -L/global/homes/m/mc29/nwchem-6.3_opt//lib/LINUX64 -L/global/homes/m/mc29/nwchem-6.3_opt//src/tools/install/lib  -o /global/homes/m/mc29/nwchem-6.3_opt//bin/LINUX64/nwchem nwchem.o stubs.o -lnwctask -lccsd -lmcscf -lselci -lmp2 -lmoints -lstepper -ldriver -loptim -lnwdft -lgradients -lcphf -lesp -lddscf -ldangchang -lguess -lhessian -lvib -lnwcutil -lrimp2 -lproperty -lnwints -lprepar -lnwmd -lnwpw -lofpw -lpaw -lpspw -lband -lnwpwlib -lnwxc -lcafe -lspace -lanalyze -lqhop -lpfft -ldplot -ldrdy -lvscf -lqmmm -lqmd -letrans -lpspw -ltce -lbq -lcons -lperfm -ldntmc -lccca -lnwcutil -lga -larmci -lpeigs -lperfm -lcons -lbq -lnwcutil -lsci_gnu   -l64to32 -lsci_gnu
