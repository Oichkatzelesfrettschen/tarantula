CC=clang
CFLAGS ?= -O2 -std=c23 -Wall -Werror
CPPFLAGS = -I../../include

all: dirlist

dirlist: dirlist.o inmemfs.o
	$(CC) $(CFLAGS) dirlist.o inmemfs.o -o $@

%.o: %.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	 rm -f dirlist dirlist.o inmemfs.o

.PHONY: all clean
