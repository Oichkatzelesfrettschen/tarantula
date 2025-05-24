# Cross-Architecture Porting Notes

This guide summarizes considerations for targeting 16‑bit, 32‑bit and
64‑bit x86 processors using the C23 standard.  The aim is to keep the
codebase portable across Intel and AMD chips while still allowing
platform specific optimisation.

## Strategy

- Introduce `<src-headers/arch.h>` which exposes `ARCH_BITS` and helper
  macros derived from `__SIZEOF_POINTER__`.
- Build common sources with `-std=c2x` and rely on the new header for
  pointer-width checks.
- Place generic assembly routines under `asm/` with per‑architecture
  variants in `asm/i16/`, `asm/i386/` and `asm/amd64/`. The build system
  selects the best match based on `ARCH_BITS`.
- Prefer compiler intrinsics over handwritten assembly except where
  specific tuning is required.

## Next Steps

1. Audit existing `.s` files and move them into the `asm/` hierarchy.
2. Update makefiles so `ARCH_BITS` chooses the correct variant.
3. Verify builds on 32‑bit and 64‑bit hosts, then attempt a 16‑bit
   cross compile.
