OBJS = kern_sched.o sched_lock.o
LIB  = libkern_sched.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
            -I../../sys -I../../sys/sys \
            -I../../sys/i386/include
CFLAGS   += $(CSTD) -DKERNEL

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)

.PHONY: all clean

