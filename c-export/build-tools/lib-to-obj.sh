D=__libtmp
mkdir $D
cd $D
ar -x $1
ld -r -o ../$2 *.o
cd ..
rm -rf $D
