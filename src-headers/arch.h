#pragma once
#ifndef ARCH_H
#define ARCH_H

/*
 * Modern architecture detection helpers for 16, 32 and 64-bit x86
 * systems. These macros rely on standard C23 features and allow the
 * codebase to adapt to Intel and AMD processors.
 */

#include <stdint.h>

#ifndef __SIZEOF_POINTER__
#  error "compiler must define __SIZEOF_POINTER__"
#endif

#define ARCH_BITS (__SIZEOF_POINTER__ * 8)
#define ARCH_16BIT (ARCH_BITS == 16)
#define ARCH_32BIT (ARCH_BITS == 32)
#define ARCH_64BIT (ARCH_BITS == 64)

#if __STDC_VERSION__ >= 202000L
#  define ARCH_UNREACHABLE() __builtin_unreachable()
#else
#  define ARCH_UNREACHABLE() ((void)0)
#endif

_Static_assert(ARCH_BITS == 16 || ARCH_BITS == 32 || ARCH_BITS == 64,
               "Unsupported architecture size");

#endif /* ARCH_H */
