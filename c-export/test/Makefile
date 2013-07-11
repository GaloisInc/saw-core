CFLAGS=-optc-I../dist/build -optc-I../cbits
PROG=test_export
${PROG}: ${PROG}.c
	ghc ${CFLAGS} -package saw-export -no-hs-main -o $@ $<

clean:
	rm -f ${PROG} ${PROG}.o
