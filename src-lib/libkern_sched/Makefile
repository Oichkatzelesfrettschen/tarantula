OBJS = kern_sched.o sched_lock.o runqueue.o
LIB  = libkern_sched.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2
CSTD ?= -std=c23
CPPFLAGS ?= -I../../sys/i386/include \
            -I../../sys -I../../sys/sys \
            -I../../src-headers -I../../src-headers/machine
CFLAGS   += $(CSTD) -DKERNEL -Wall

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean

