CC = gcc
CFLAGS = -Wall -O2
LDLIBS = -L.. -Wl,-rpath=.. -lpathtrans -pthread -ldl

TARGETS = test_translation test_path_database test_disable_env \
          test_link_unlink test_chdir_getcwd test_execve

all: $(TARGETS)

run: all
	./run_tests.sh

test_translation: test_translation.c
	$(CC) $(CFLAGS) -o $@ $^

test_path_database: test_path_database.c
	$(CC) $(CFLAGS) -I../include $^ $(LDLIBS) -o $@

test_disable_env: test_disable_env.c
	$(CC) $(CFLAGS) -o $@ $^

test_link_unlink: test_link_unlink.c
	$(CC) $(CFLAGS) -o $@ $^ $(LDLIBS)

test_chdir_getcwd: test_chdir_getcwd.c
	$(CC) $(CFLAGS) -o $@ $^ $(LDLIBS)

test_execve: test_execve.c
	$(CC) $(CFLAGS) -o $@ $^ $(LDLIBS)

clean:
	rm -f $(TARGETS)
	rm -rf /tmp/pathtrans_test*

.PHONY: all run clean
