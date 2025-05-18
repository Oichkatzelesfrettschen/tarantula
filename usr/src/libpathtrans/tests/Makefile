
CC = gcc
CFLAGS = -Wall -O2
LDFLAGS =

# Allow extra flags from parent makefiles
CFLAGS += $(CFLAGS_EXTRA)
LDFLAGS += $(LDFLAGS_EXTRA)

all: test_translation

run: all run_tests.sh
	./run_tests.sh

test_translation: test_translation.c
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	rm -f test_translation
	rm -rf /tmp/pathtrans_test*

.PHONY: all run clean

