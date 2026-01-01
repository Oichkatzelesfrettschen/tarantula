#pragma once
/*-
 * Simplified system prototypes for user-space builds.
 * Derived from the 4.4BSD-Lite2 kernel's systm.h.
 */

#ifndef _SYS_SYSTM_H_
#define _SYS_SYSTM_H_

#include <stdnoreturn.h>

extern int securelevel;      /* system security level */
extern const char *panicstr; /* panic message */
extern char version[];       /* system version */
extern char copyright[];     /* system copyright */

_Noreturn void panic(const char *, ...);
int printf(const char *, ...);
void bcopy(const void *from, void *to, u_int len);
void bzero(void *buf, u_int len);

#endif /* _SYS_SYSTM_H_ */
