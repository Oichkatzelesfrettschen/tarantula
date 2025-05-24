CC ?= cc
CFLAGS ?= -O2 -std=c2x
CXX ?= c++
CXXFLAGS ?= -O2 -std=c++23
CPPFLAGS = -I../tests/include -I../src-headers -I../src-headers/machine -I../src-kernel
LIBS = ../src-kernel/libkern_stubs.a ../src-lib/libipc/libipc.a

OBJS = test_kern.o fs_open.o pm_entry.o vm_entry.o sched_stub.o mock_vm.o

all: test_kern spinlock_cpp

test_kern: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LIBS) -o $@

spinlock_cpp: test_spinlock.o
	$(CXX) $(CXXFLAGS) test_spinlock.o -o $@

fs_open.o: ../src-uland/fs-server/fs_open.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

pm_entry.o: ../src-uland/servers/proc_manager/pm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

vm_entry.o: ../src-uland/libvm/vm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

mock_vm.o: mock_vm.c
	$(CC) -I../tests/include $(CFLAGS) -c $< -o $@

sched_stub.o: sched_stub.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

test_spinlock.o: test_spinlock.cpp
	$(CXX) $(CXXFLAGS) -I../src-headers -c $< -o $@

clean:
	rm -f $(OBJS) test_kern spinlock_cpp test_spinlock.o

.PHONY: all clean
