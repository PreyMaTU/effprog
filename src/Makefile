FILES=HEADER.html Makefile magichex.c reference-output
CFLAGS=-Wall -O3
#CFLAGS=-Wall -O -g
LDFLAGS=-g

magichex: magichex.o

test1: magichex
	./magichex 3 2

test2: magichex
	./magichex 3 0

measure: magichex
	perf stat -e cycles:u -e instructions:u -e branches:u -e branch-misses:u -e L1-dcache-load-misses:u ./magichex 4 3 14 33 30 34 39 6 24 20 |\
	grep -v solution| \
	awk '/^leafs visited:/ {printf("\0")} /^leafs visited:/,/^$$/ {next} 1'|\
	sort -z|\
	tr '\0' '\n\n' |\
	diff -u reference-output -

nocheck: magichex
	perf stat -e cycles:u -e instructions:u -e branches:u -e branch-misses:u -e L1-dcache-load-misses:u ./magichex 4 3 14 33 30 34 39 6 24 20

dist:
	mkdir effizienz-aufgabe23
	cp -p $(FILES) effizienz-aufgabe23
	tar cfz effizienz-aufgabe23.tar.gz effizienz-aufgabe23
	rm -rf effizienz-aufgabe23

clean:
	rm -f magichex magichex.o
