F=__liblist
SCT=libsawcoretemp.a
rm -f $F
for l in `cat build-tools/base-deps` ; do
  ls `ghc --print-libdir`/$l/HS*.o >> $F
done
ls cabal-dev/lib/*/ghc-7.6.3/HS*.o >> $F
ar -r ${SCT} `cat $F`
libtool -static -o libsawcore.a cabal-dev/lib/abcBridge-*/ghc-*/libabc.a ${SCT}
rm -f ${SCT}
rm -f $F
