CC=gcc
CFLAGS=-Wall -O2
LDLIBS=-L.. -Wl,-rpath=.. -lpathtrans -pthread -ldl

all: demo

demo: demo.c
$(CC) $(CFLAGS) -o $@ $< $(LDLIBS)

clean:
rm -f demo

.PHONY: all clean
