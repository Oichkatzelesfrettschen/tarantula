SRCS = fs_open.c $(wildcard vfs_*.c)
OBJS = $(SRCS:.c=.o)
PROG = fs_server

CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c23
CPPFLAGS ?= -I../../src-headers -I../../src-headers/machine \
            -I../../sys -I../../sys/sys \
            -I../../sys/i386/include -I../../include
CFLAGS   += $(CSTD) -DKERNEL -Wall -Werror

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CPPFLAGS) $(CFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean
