CC=clang
CFLAGS ?= -O2 -std=c23 -Wall -Werror
CPPFLAGS = -I../../include -I../../src-headers
LIBPOSIX = ../../src-lib/libposix/libposix.a

all: dirlist signal_test

dirlist: dirlist.o inmemfs.o
	$(CC) $(CFLAGS) dirlist.o inmemfs.o -o $@

signal_test: signal_test.o
	$(CC) $(CFLAGS) signal_test.o $(LIBPOSIX) -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f dirlist signal_test *.o

.PHONY: all clean
