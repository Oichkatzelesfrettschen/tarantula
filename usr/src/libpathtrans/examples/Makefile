CC=gcc
CFLAGS=-Wall -O2
CPPFLAGS=-I../../../src-headers -I../include
LIBDIR?=../../../../src-lib/libpathtrans
LDLIBS=-L$(LIBDIR) -Wl,-rpath=$(LIBDIR) -lpathtrans -pthread -ldl

all: demo

demo: demo.c
$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

clean:
rm -f demo

.PHONY: all clean
