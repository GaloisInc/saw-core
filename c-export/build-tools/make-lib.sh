F=__liblist
SCT=libsawcoretemp.a
RTS=`ghc --print-libdir`/libHSrts.a
rm -f $F
for l in `cat build-tools/base-deps` ; do
  ls `ghc --print-libdir`/$l/HS*.o >> $F
done
ls cabal-dev/lib/*/ghc-7.6.3/HS*.o >> $F
ar -r ${SCT} `cat $F`
ABC=`ls cabal-dev/lib/abcBridge-*/ghc-*/libabc.a`
libtool -static -o libsawcore.a ${RTS} ${ABC} ${SCT}
rm -f ${SCT}
rm -f $F
