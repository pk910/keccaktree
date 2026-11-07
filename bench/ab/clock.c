/* core clock estimate: a dependent chain of 1-cycle adds, ns per add = 1/f */
#include <stdio.h>
#include <stdint.h>
#include <time.h>
int main(void) {
    struct timespec a, b;
    uint64_t x = 0, n = 1u << 28;
    double best = 1e9;
    for (int rep = 0; rep < 5; rep++) {
        clock_gettime(CLOCK_MONOTONIC, &a);
        for (uint64_t i = 0; i < n; i++) {
#if defined(__aarch64__)
            __asm__ volatile("add %0, %0, #1\n\tadd %0, %0, #1\n\tadd %0, %0, #1\n\tadd %0, %0, #1\n\t"
                             "add %0, %0, #1\n\tadd %0, %0, #1\n\tadd %0, %0, #1\n\tadd %0, %0, #1" : "+r"(x));
#else
            __asm__ volatile("add $1, %0\n\tadd $1, %0\n\tadd $1, %0\n\tadd $1, %0\n\t"
                             "add $1, %0\n\tadd $1, %0\n\tadd $1, %0\n\tadd $1, %0" : "+r"(x));
#endif
        }
        clock_gettime(CLOCK_MONOTONIC, &b);
        double s = (b.tv_sec - a.tv_sec) + (b.tv_nsec - a.tv_nsec) * 1e-9;
        if (s < best) best = s;
    }
    printf("clock: %.3f GHz (dependent add chain, %llu adds in %.3f s, x=%llu)\n", 8.0 * n / best / 1e9,
           (unsigned long long)(8 * n), best, (unsigned long long)x);
    return 0;
}
