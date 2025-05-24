#ifndef ARCH_H
#define ARCH_H

/*
 * Modern architecture detection helpers for 16, 32 and 64-bit x86
 * systems. These macros rely on standard C23 features and allow the
 * codebase to adapt to Intel and AMD processors.
 */

#include <stdint.h>

#if defined(__SIZEOF_POINTER__)
#  if __SIZEOF_POINTER__ == 2
#    define ARCH_16BIT 1
#  elif __SIZEOF_POINTER__ == 4
#    define ARCH_32BIT 1
#  elif __SIZEOF_POINTER__ == 8
#    define ARCH_64BIT 1
#  else
#    error "Unsupported pointer width"
#  endif
#else
#  error "__SIZEOF_POINTER__ not defined"
#endif

#if defined(ARCH_64BIT)
#  define ARCH_BITS 64
#elif defined(ARCH_32BIT)
#  define ARCH_BITS 32
#else
#  define ARCH_BITS 16
#endif

#if __STDC_VERSION__ >= 202000L
#  define ARCH_UNREACHABLE() __builtin_unreachable()
#else
#  define ARCH_UNREACHABLE() ((void)0)
#endif

_Static_assert(ARCH_BITS == 16 || ARCH_BITS == 32 || ARCH_BITS == 64,
               "Unsupported architecture size");

#endif /* ARCH_H */
