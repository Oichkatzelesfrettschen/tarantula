OBJS = kern_proc.o
PROG = proc_manager
CC ?= cc
CFLAGS ?= -O2
CPPFLAGS ?= -I../../../src-headers -I../../../sys -I../../../sys/i386/include

all: $(PROG)

$(PROG): $(OBJS)
	$(CC) $(CFLAGS) $(CPPFLAGS) $(OBJS) -o $@

%.o: %.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(PROG)

