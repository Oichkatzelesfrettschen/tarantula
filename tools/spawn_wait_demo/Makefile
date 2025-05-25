CC ?= cc
CFLAGS ?= -O2 -std=c2x -Wall -Werror
CPPFLAGS ?= -I../../src-headers -I../../include
LIBS = ../../src-kernel/libkern_stubs.a ../../src-lib/libipc/libipc.a
	
PROG = spawn_wait_demo

all: $(PROG)

$(PROG): spawn_wait_demo.o $(LIBS)
	$(CC) $(CFLAGS) spawn_wait_demo.o $(LIBS) -o $@
	
spawn_wait_demo.o: spawn_wait_demo.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f spawn_wait_demo.o $(PROG)

.PHONY: all clean
