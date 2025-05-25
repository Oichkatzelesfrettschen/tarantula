OBJS = kern_proc.o pm_entry.o
PROG = proc_manager
CC ?= cc
CFLAGS ?= -O2
CSTD ?= -std=c23
CPPFLAGS ?= -I../../../src-headers -I../../../src-headers/machine \
            -I../../../sys -I../../../sys/sys \
            -I../../../sys/i386/include -I../../../include
CFLAGS   += $(CSTD) -DKERNEL -Wall -Werror

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

