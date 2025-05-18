
CC = gcc
CFLAGS = -Wall -O2
LDFLAGS =

# Allow extra flags from parent makefiles
CFLAGS += $(CFLAGS_EXTRA)
LDFLAGS += $(LDFLAGS_EXTRA)

all: pathtrans_db

pathtrans_db: pathtrans_db.c
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f pathtrans_db

.PHONY: all clean

