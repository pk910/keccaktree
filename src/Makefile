# keccaktree - batched keccak256 for Merkle trees (hashtree-compatible API)
OUT_DIR ?= $(CURDIR)/../build
OBJ_DIR := $(OUT_DIR)/obj
LIB_DIR := $(OUT_DIR)/lib
$(shell mkdir -p $(OBJ_DIR) $(LIB_DIR))

CFLAGS ?= -g -Wall -Werror -O3
override CFLAGS += -fpic
libname = $(LIB_DIR)/libkeccaktree.a

ARCH := $(shell $(CC) -dumpmachine)
ifneq ($(findstring mingw,$(ARCH)),)
# gcc on Windows x64 does not realign the stack for 32/64-byte spills (gcc
# bug 54412); have the assembler emit unaligned moves instead.
override CFLAGS += -Wa,-muse-unaligned-vector-move
endif
ifneq ($(findstring x86_64,$(ARCH)),)
OBJ_LIST = $(OBJ_DIR)/keccak256_avx512_x8.o $(OBJ_DIR)/keccak256_avx512vl_x4.o $(OBJ_DIR)/keccak256_avx2_x4.o
else ifneq ($(findstring aarch64,$(ARCH))$(findstring arm64,$(ARCH)),)
OBJ_LIST = $(OBJ_DIR)/keccak256_neon_x2.o $(OBJ_DIR)/keccak256_sha3_x2.o
endif
OBJ_LIST += $(OBJ_DIR)/keccak256_generic.o $(OBJ_DIR)/keccaktree.o

all: $(libname) test bench

# generated sources are committed; regenerate with `make gen`
gen:
	python3 ../tools/gen_core.py > keccak256_core.inc
	python3 ../tools/gen_core.py --ternlog > keccak256_core_tl.inc

$(OBJ_DIR)/keccak256_avx512_x8.o: keccak256_avx512_x8.c keccak256_core_tl.inc
	$(CC) $(CFLAGS) -mavx512f -mavx512vl -c $< -o $@
$(OBJ_DIR)/keccak256_avx512vl_x4.o: keccak256_avx2_x4.c keccak256_core_tl.inc
	$(CC) $(CFLAGS) -DKT_AVX512VL -mavx2 -mavx512f -mavx512vl -c $< -o $@
$(OBJ_DIR)/keccak256_avx2_x4.o: keccak256_avx2_x4.c keccak256_core.inc
	$(CC) $(CFLAGS) -mavx2 -c $< -o $@
$(OBJ_DIR)/keccak256_sha3_x2.o: keccak256_neon_x2.c keccak256_core.inc
	$(CC) $(CFLAGS) -DKT_SHA3 -march=armv8.2-a+sha3 -c $< -o $@
$(OBJ_DIR)/%.o: %.c keccak256_core.inc keccaktree.h
	$(CC) $(CFLAGS) -c $< -o $@

$(libname): $(OBJ_LIST)
	$(AR) rcs $@ $(OBJ_LIST)

test: test.c $(libname)
	$(CC) $(CFLAGS) -o $(OUT_DIR)/test test.c -L$(LIB_DIR) -lkeccaktree

# HASHTREE=1 links $(HASHTREE_DIR)/build/lib/libhashtree.a (build hashtree first) for the sha256 comparison
ifeq ($(HASHTREE),1)
HASHTREE_DIR ?= ../../hashtree
BENCH_EXTRA = -DHAVE_HASHTREE -I$(HASHTREE_DIR)/src -L$(HASHTREE_DIR)/build/lib -lhashtree
endif
bench: bench.c $(libname)
	$(CC) $(CFLAGS) -o $(OUT_DIR)/bench bench.c -L$(LIB_DIR) -lkeccaktree $(BENCH_EXTRA)

clean:
	rm -rf $(OUT_DIR)

.PHONY: all test bench clean gen
