# Cross-Architecture Porting Notes

This guide summarizes considerations for targeting 16‑bit, 32‑bit and
64‑bit x86 processors using the C23 standard.  The aim is to keep the
codebase portable across Intel and AMD chips while still allowing
platform specific optimisation.

## Strategy

- Introduce `<src-headers/arch.h>` which exposes `ARCH_BITS` and helper
  macros derived from `__SIZEOF_POINTER__`.
- The header defines `ARCH_16BIT`, `ARCH_32BIT`, `ARCH_64BIT` and the
  `ARCH_UNREACHABLE()` helper. Source files include it and perform checks
  such as `#if ARCH_BITS == 32` when special casing logic.
- Build common sources with `-std=c2x` and rely on the new header for
  pointer-width checks.
- Place generic assembly routines under `asm/` with per‑architecture
  variants in `asm/i16/`, `asm/i386/` and `asm/amd64/`. The build system
  selects the best match based on `ARCH_BITS`.
- Prefer compiler intrinsics over handwritten assembly except where
  specific tuning is required.

### Example usage

Include the header and branch on the pointer width when implementing
architecture specific code:

```c
#include <arch.h>

#if ARCH_64BIT
    /* 64-bit optimised path */
#else
    /* generic fallback */
#endif
```

The CMake build installs `arch.h` under `${CMAKE_INSTALL_PREFIX}/include`
so out-of-tree projects can rely on it as well.

## Next Steps

1. Audit existing `.s` files and move them into the `asm/` hierarchy.
2. Update makefiles so `ARCH_BITS` chooses the correct variant.
3. Verify builds on 32‑bit and 64‑bit hosts, then attempt a 16‑bit
   cross compile.
