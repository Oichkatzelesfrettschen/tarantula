#pragma once
#ifndef TIMER_H
#define TIMER_H

#include <stdint.h>
#include <sys/types.h>

void timer_init(void);
void timer_add_sleep(pid_t pid, uint64_t ns);
uint64_t timer_get_sleep(pid_t pid);

#endif /* TIMER_H */
