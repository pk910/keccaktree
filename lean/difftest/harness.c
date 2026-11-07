/* Differential-test harness: reads initial states (stdin), runs each test snippet on the
   real CPU (or under qemu-user / Intel SDE), prints the final state (stdout).
   State text format: see README.md in this directory. */
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define W 4096                 /* words per memory region */
#define MASK56 0x00ffffffffffffffULL

#if defined(__x86_64__)
#  define NG 16
#  ifdef AVX512
#    define NV 32
#    define NL 8
#    define NK 8
#  else
#    define NV 16
#    define NL 4
#    define NK 0
#  endif
#  define OFF_G 0
#  define OFF_FL 128
#  define OFF_WHICH 136
#  define OFF_V 256
#  define OFF_K 2304
#  define STATE_BYTES 2432
#elif defined(__aarch64__)
#  define NG 32               /* x0..x30, sp */
#  define NV 32
#  define NL 2
#  define NK 0
#  define OFF_G 0
#  define OFF_FL 256          /* nzcv */
#  define OFF_WHICH 264
#  define OFF_V 512
#  define STATE_BYTES 1024
#elif defined(__riscv)
#  define NG 32
#  define NV 32
#  define NL 8                /* lanes stored (VLEN up to 512) */
#  define NK 0
#  define OFF_G 0
#  define OFF_FL 256          /* unused */
#  define OFF_VL 264
#  define OFF_WHICH 272
#  define OFF_V 512
#  define STATE_BYTES 2560
#endif

#if defined(__aarch64__)
#  define VSTRIDE 2
#else
#  define VSTRIDE 8
#endif

extern unsigned char kt_in[], kt_out[];
extern void kt_run(void *target);
extern void *kt_cases[];
extern char *kt_ro_addr, kt_text0[];
#define kt_ro kt_ro_addr

static uint64_t *base[5];
static uint64_t *snap[4];
static sigjmp_buf env;
static volatile int fault;

static uint64_t mix(uint64_t seed, uint64_t r, uint64_t q) {
  uint64_t z = seed ^ (r << 56) ^ (q * 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

static uint64_t conv(uint64_t w, int isptr) {
  if (!isptr) return w;
  uint64_t r = w >> 56;
  if (r >= 1 && r <= 3) return (uint64_t)base[r] + (w & MASK56);
  if (r == 4) return (uint64_t)kt_ro + (w & MASK56);
  return w;
}

static void handler(int sig, siginfo_t *si, void *uc) { (void)si; (void)uc; fault = sig; siglongjmp(env, 1); }

int main(void) {
  for (int r = 1; r <= 3; r++) {
    base[r] = mmap(NULL, W * 8, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    snap[r] = malloc(W * 8);
  }
  static char altstack[1 << 16];
  stack_t ss = {.ss_sp = altstack, .ss_size = sizeof altstack, .ss_flags = 0};
  sigaltstack(&ss, NULL);
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = handler;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK | SA_NODEFER;
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
  sigaction(SIGILL, &sa, NULL);
  sigaction(SIGFPE, &sa, NULL);
  printf("B 1 %llx\nB 2 %llx\nB 3 %llx\nB 4 %llx\nT %llx\n", (unsigned long long)base[1], (unsigned long long)base[2],
         (unsigned long long)base[3], (unsigned long long)kt_ro, (unsigned long long)kt_text0);
  char line[4096];
  long cidx = -1, ncase = 0;
  unsigned long long seed = 0;
  int zf = 0, cf = 0, nf = 0, vf = 0;
  unsigned long vl = 0;
  struct { int r; long q; uint64_t w; int p; } ov[64];
  int nov = 0;
  while (fgets(line, sizeof line, stdin)) {
    char *p = line;
    if (line[0] == 'C') {
      sscanf(line + 1, "%ld %llx", &cidx, &seed);
      memset(kt_in, 0, STATE_BYTES);
      nov = 0; zf = cf = nf = vf = 0; vl = 0;
    } else if (line[0] == 'G') {
      int i; unsigned long long w; char tag[8] = "";
      sscanf(line + 1, "%d %llx %7s", &i, &w, tag);
      if (i < NG) ((uint64_t *)(kt_in + OFF_G))[i] = conv(w, tag[0] == 'P');
    } else if (line[0] == 'V') {
      int i, n; p = line + 1;
      sscanf(p, "%d%n", &i, &n); p += n;
      for (int l = 0; l < 8; l++) {
        unsigned long long w; sscanf(p, "%llx%n", &w, &n); p += n;
        if (i < NV && l < NL) ((uint64_t *)(kt_in + OFF_V))[i * VSTRIDE + l] = w;
      }
    } else if (line[0] == 'K') {
#if NK
      int i; unsigned long k; sscanf(line + 1, "%d %lu", &i, &k);
      ((uint64_t *)(kt_in + OFF_K))[i] = k;
#endif
    } else if (line[0] == 'F') {
      sscanf(line + 1, "%d %d %d %d", &zf, &cf, &nf, &vf);
    } else if (line[0] == 'L') {
      sscanf(line + 1, "%lu", &vl);
    } else if (line[0] == 'M') {
      unsigned long long w; char tag[8] = "";
      sscanf(line + 1, "%d %ld %llx %7s", &ov[nov].r, &ov[nov].q, &w, tag);
      ov[nov].w = w; ov[nov].p = tag[0] == 'P'; nov++;
    } else if (line[0] == 'E') {
      for (int r = 1; r <= 3; r++)
        for (long q = 0; q < W; q++) base[r][q] = mix(seed, r, q);
      for (int i = 0; i < nov; i++)
        if (ov[i].r >= 1 && ov[i].r <= 3 && ov[i].q >= 0 && ov[i].q < W) base[ov[i].r][ov[i].q] = conv(ov[i].w, ov[i].p);
      for (int r = 1; r <= 3; r++) memcpy(snap[r], base[r], W * 8);
#if defined(__x86_64__)
      *(uint64_t *)(kt_in + OFF_FL) = 0x202 | (zf ? 0x40 : 0) | (cf ? 1 : 0);
#elif defined(__aarch64__)
      *(uint64_t *)(kt_in + OFF_FL) = ((uint64_t)nf << 31) | ((uint64_t)zf << 30) | ((uint64_t)cf << 29) | ((uint64_t)vf << 28);
#elif defined(__riscv)
      *(uint64_t *)(kt_in + OFF_VL) = vl;
#endif
      memset(kt_out, 0, STATE_BYTES);
      fault = 0;
      if (sigsetjmp(env, 1) == 0) kt_run(kt_cases[cidx]);
      printf("C %ld\n", ncase++);
      if (fault) { printf("S %d\nE\n", fault); continue; }
      printf("W %llu\n", (unsigned long long)*(uint64_t *)(kt_out + OFF_WHICH));
      for (int i = 0; i < NG; i++) printf("G %d %llx\n", i, (unsigned long long)((uint64_t *)(kt_out + OFF_G))[i]);
#if defined(__x86_64__)
      uint64_t fl = *(uint64_t *)(kt_out + OFF_FL);
      printf("F %d %d 0 0\n", (int)((fl >> 6) & 1), (int)(fl & 1));
#elif defined(__aarch64__)
      uint64_t fl = *(uint64_t *)(kt_out + OFF_FL);
      printf("F %d %d %d %d\n", (int)((fl >> 30) & 1), (int)((fl >> 29) & 1), (int)((fl >> 31) & 1), (int)((fl >> 28) & 1));
#else
      printf("F 0 0 0 0\nL %llu\n", (unsigned long long)*(uint64_t *)(kt_out + OFF_VL));
#endif
      for (int i = 0; i < NV; i++) {
        printf("V %d", i);
        for (int l = 0; l < NL; l++) printf(" %llx", (unsigned long long)((uint64_t *)(kt_out + OFF_V))[i * VSTRIDE + l]);
        printf("\n");
      }
#if NK
      for (int i = 0; i < NK; i++) printf("K %d %llu\n", i, (unsigned long long)(((uint64_t *)(kt_out + OFF_K))[i] & 0xffff));
#endif
      for (int r = 1; r <= 3; r++)
        for (long q = 0; q < W; q++)
          if (base[r][q] != snap[r][q]) printf("M %d %ld %llx\n", r, q, (unsigned long long)base[r][q]);
      printf("E\n");
    }
  }
  return 0;
}
