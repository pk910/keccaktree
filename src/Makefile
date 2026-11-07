# keccaktree - batched keccak256 for Merkle trees (hashtree-compatible API)
OUT_DIR ?= $(CURDIR)/../build
OBJ_DIR := $(OUT_DIR)/obj
LIB_DIR := $(OUT_DIR)/lib
$(shell mkdir -p $(OBJ_DIR) $(LIB_DIR))

CFLAGS ?= -g -Wall -Werror -O3
ASFLAGS ?= -g
override ASFLAGS += -fpic
override CFLAGS += -fpic
libname = $(LIB_DIR)/libkeccaktree.a

ARCH := $(shell $(CC) -dumpmachine)
ifneq ($(findstring mingw,$(ARCH)),)
# gcc on Windows x64 does not realign the stack for 32/64-byte spills (gcc
# bug 54412); have the assembler emit unaligned moves instead.
override CFLAGS += -Wa,-muse-unaligned-vector-move
endif
ifneq ($(findstring x86_64,$(ARCH)),)
X86_KERNELS = avx512_x8 avx512_x9 avx512vl_x4 avx512_x8b5 avx512_x8b10 avx512_x8al avx512_x9b avx512_x9c avx2_x4 avx2_x8 avx2_x9 avx2_x10 avx2_x5 avx2_x6 avx2_x2 x86_x1
OBJ_LIST = $(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(X86_KERNELS))
else ifneq ($(findstring aarch64,$(ARCH))$(findstring arm64,$(ARCH)),)
ARM_KERNELS = neon_x2 sha3_x2 scalar_x1 sha3_x3 sha3_x3r neon_x3
OBJ_LIST = $(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(ARM_KERNELS))
else ifneq ($(findstring riscv64,$(ARCH)),)
# the kernels enable their extensions with .option arch, the C code stays rv64gc
RISCV_KERNELS = rv64_x1 zbb_x1 rvv rvv_zvkb
OBJ_LIST = $(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(RISCV_KERNELS))
endif
OBJ_LIST += $(OBJ_DIR)/keccak256_generic.o $(OBJ_DIR)/keccaktree.o

all: $(libname) test bench

lib: $(libname)

# one .S per kernel, built on the shared round and frame macros (.inc)
X86_INC = keccak256_x86_frame.inc keccak256_avx512.inc keccak256_avx2.inc keccak256_avx2_pair.inc keccak256_x86_x1.inc keccak256_x86_scalar.inc
ARM_INC = keccak256_arm_frame.inc keccak256_neon.inc keccak256_asimd.inc keccak256_sha3.inc keccak256_scalar.inc keccak256_scalar_ror.inc
$(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(X86_KERNELS)): $(OBJ_DIR)/keccak256_%.o: keccak256_%.S $(X86_INC)
	$(CC) $(ASFLAGS) -c $< -o $@
$(OBJ_DIR)/keccak256_avx2_x10.o: keccak256_avx2_x9.S
$(OBJ_DIR)/keccak256_avx512_x9.o $(OBJ_DIR)/keccak256_avx512_x8b5.o $(OBJ_DIR)/keccak256_avx512_x8b10.o $(OBJ_DIR)/keccak256_avx512_x8al.o $(OBJ_DIR)/keccak256_avx512_x9b.o $(OBJ_DIR)/keccak256_avx512_x9c.o: keccak256_avx512_x8.S
$(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(ARM_KERNELS)): $(OBJ_DIR)/keccak256_%.o: keccak256_%.S $(ARM_INC)
	$(CC) $(ASFLAGS) -c $< -o $@
RISCV_INC = keccak256_riscv_frame.inc keccak256_rv64.inc keccak256_rvv.inc
$(patsubst %,$(OBJ_DIR)/keccak256_%.o,$(RISCV_KERNELS)): $(OBJ_DIR)/keccak256_%.o: keccak256_%.S $(RISCV_INC)
	$(CC) $(ASFLAGS) -c $< -o $@
$(OBJ_DIR)/%.o: %.c keccaktree.h
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

.PHONY: all lib test bench clean
