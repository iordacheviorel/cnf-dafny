all:
	~/software/dafny/dafny /verifySeparately *.dfy

clean:
	rm -f *.dll
	rm -f *.mdb
	rm -f *.exe
