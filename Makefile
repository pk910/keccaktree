# Builds the C library, tests and benchmark into build/ (see src/Makefile).
all:
	$(MAKE) -C src all

libkeccaktree:
	$(MAKE) -C src lib

test:
	$(MAKE) -C src test

bench:
	$(MAKE) -C src bench

clean:
	$(MAKE) -C src clean

.PHONY: all libkeccaktree test bench clean
