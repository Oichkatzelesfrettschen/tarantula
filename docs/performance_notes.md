# Performance Notes

## Vectorized `vfs_bufstats`

A microbenchmark located at `tools/bench_vfs_bufstats.c` compares the new
vectorized zeroing routine against the previous scalar loop. On the CI
container (x86-64, clang -O2) running 10 million iterations:

```
scalar 0.0021s
vector 0.0020s
```

The AVX2 path offers a small win over the scalar implementation. Systems
without AVX2/SSE2 automatically fall back to the portable code path.
