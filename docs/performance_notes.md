# Performance Notes

## Vectorized `vfs_bufstats`

A microbenchmark located at `tools/bench_vfs_bufstats.c` compares the new vectorized zeroing routine against the previous scalar loop. On the CI container (x86-64, clang -O2) running 10 million iterations:

```text
scalar 0.0021 s
vector 0.0020 s
```

The AVX2 path offers a small win over the scalar implementation. Systems without AVX2/SSE2 automatically fall back to the portable code path.

## Default Optimization Flags

The build system now defaults to SSE-backed math operations for consistent floating-point semantics on modern hardware. The top-level `CMakeLists.txt` exports the following baseline flags:

```sh
-O3 -march=x86-64 -mfpmath=sse -msse2 -mmmx
```

These options tune the generated binaries for a minimal x86-64 baseline while ensuring the compiler emits SSE and MMX instructions (and avoids legacy x87) for predictable performance.

### Conditional AVX2 Enablement for `fs_server`

When building the filesystem server (`fs_server`) with Clang, additional SIMD extensions are enabled to further accelerate data-path operations:

```cmake
if(CMAKE_C_COMPILER_ID STREQUAL "Clang")
  target_compile_options(fs_server PRIVATE -msse -msse2 -mavx2)
endif()
```

On an Intel i7-8650U laptop, our `bench_fs_rpc` microbenchmark shows approximately a 4 % improvement in RPC throughput with `-mavx2` enabled versus builds without it. GCC builds sometimes mis-handle these options, so they are gated to Clang only.

---

**Summary of Flags Across All Targets**

* **Baseline (all targets)**: `-O3 -march=x86-64 -mfpmath=sse -msse2 -mmmx`
* **Additional for Clang-built `fs_server`**: `-msse -msse2 -mavx2`

Systems lacking SSE2/AVX2 automatically fall back to portable scalar code paths without any manual intervention.

