
all:
	@echo "No tests yet"
clean:
	@true

CC = gcc
CFLAGS = -Wall -O2

all: test_translation

run: all run_tests.sh
	./run_tests.sh

test_translation: test_translation.c
	$(CC) $(CFLAGS) -o $@ $^

clean:
	rm -f test_translation
	rm -rf /tmp/pathtrans_test*

.PHONY: all run clean

