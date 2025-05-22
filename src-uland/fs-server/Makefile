SRCS = fs_open.c $(wildcard vfs_*.c)
OBJS = $(SRCS:.c=.o)
PROG = fs_server

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c2x
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
            -I../../include -I../../sys -I../../sys/sys \
            -I../../sys/i386/include
CFLAGS   += $(CSTD) -DKERNEL

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean
