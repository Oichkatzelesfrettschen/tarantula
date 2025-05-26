#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#ifndef LEN
#define LEN 32
#endif

static inline void zero_counts_scalar(int *c, size_t len) {
    for (size_t i = 0; i < len; ++i)
        c[i] = 0;
}

static inline void zero_counts_vector(int *c, size_t len) {
    size_t j = 0;
#if defined(__AVX2__)
    if (__builtin_cpu_supports("avx2")) {
        __m256i z = _mm256_setzero_si256();
        for (; j + 8 <= len; j += 8)
            _mm256_storeu_si256((__m256i *)(c + j), z);
    }
#endif
#if defined(__SSE2__)
    if (j < len && __builtin_cpu_supports("sse2")) {
        __m128i z = _mm_setzero_si128();
        for (; j + 4 <= len; j += 4)
            _mm_storeu_si128((__m128i *)(c + j), z);
    }
#endif
    for (; j < len; ++j)
        c[j] = 0;
}

static double bench(void (*fn)(int *, size_t)) {
    volatile int sink;
    int c[LEN];
    struct timespec ts1, ts2;
    clock_gettime(CLOCK_MONOTONIC, &ts1);
    for (int i = 0; i < 10000000; ++i) {
        fn(c, LEN);
        sink = c[0];
    }
    clock_gettime(CLOCK_MONOTONIC, &ts2);
    return (ts2.tv_sec - ts1.tv_sec) + (ts2.tv_nsec - ts1.tv_nsec)/1e9 + sink*0;
}

int main(void) {
    double s = bench(zero_counts_scalar);
    double v = bench(zero_counts_vector);
    printf("scalar %f\nvector %f\n", s, v);
    return 0;
}
