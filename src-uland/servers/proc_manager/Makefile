OBJS = kern_proc.o pm_entry.o
PROG = proc_manager
CC ?= cc
CFLAGS ?= -O2
CLANG_TIDY ?= ../../../tools/run_clang_tidy.sh
CPPFLAGS ?= -I../../../src-headers -I../../../src-headers/machine \
            -I../../../include -I../../../sys -I../../../sys/sys \
            -I../../../sys/i386/include
CFLAGS   += -DKERNEL

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

.PHONY: all clean tidy

tidy:
	$(CLANG_TIDY) $(OBJS:.o=.c) -- $(CC) $(CPPFLAGS) $(CFLAGS)
	
