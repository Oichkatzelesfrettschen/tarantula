CC = gcc
CFLAGS = -Wall -O2

all: pathtrans_db

pathtrans_db: pathtrans_db.c
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm -f pathtrans_db

.PHONY: all clean
