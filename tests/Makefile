CC ?= cc
CFLAGS ?= -O2 -std=c2x
CPPFLAGS = -I../tests/include -I../include -I../src-headers -I../src-headers/machine -I../src-kernel
LIBS = ../src-kernel/libkern_stubs.a

OBJS = test_kern.o fs_open.o pm_entry.o vm_entry.o mock_vm.o

all: test_kern

test_kern: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LIBS) -o $@

fs_open.o: ../src-uland/fs-server/fs_open.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

pm_entry.o: ../src-uland/servers/proc_manager/pm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

vm_entry.o: ../src-uland/libvm/vm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

mock_vm.o: mock_vm.c
	$(CC) -I../tests/include $(CFLAGS) -c $< -o $@

clean:
	 rm -f $(OBJS) test_kern

.PHONY: all clean
