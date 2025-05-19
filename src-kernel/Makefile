OBJS = sched_hooks.o vm_hooks.o vfs_hooks.o
LIB = libkern_stubs.a

CC ?= cc
AR ?= ar
CFLAGS ?= -O2

all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)
