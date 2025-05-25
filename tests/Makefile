CC ?= clang
CXX ?= clang++
CFLAGS ?= -O2 -std=c23 -Wall -Werror
CXXFLAGS ?= -O2 -std=c++23 -Wall -Werror
CPPFLAGS = -I../tests/include -I../src-headers -I../src-headers/machine -I../src-kernel -I../include
LIBS = ../src-kernel/libkern_stubs.a ../src-lib/libipc/libipc.a \
       ../src-lib/libtimer/libtimer.a

OBJS = test_kern.o fs_open.o pm_entry.o vm_entry.o sched_stub.o mock_vm.o
MAILBOX_OBJS = test_mailbox.o
TIMER_OBJS = test_timer.o

all: test_kern spinlock_cpp mailbox_test timer_test

test_kern: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LIBS) -o $@

spinlock_cpp: test_spinlock.o
	$(CXX) $(CXXFLAGS) test_spinlock.o -o $@

mailbox_test: $(MAILBOX_OBJS)
	$(CC) $(CFLAGS) $(MAILBOX_OBJS) $(LIBS) -o $@

timer_test: $(TIMER_OBJS)
	$(CC) $(CFLAGS) $(TIMER_OBJS) $(LIBS) -o $@

fs_open.o: ../src-uland/fs-server/fs_open.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

pm_entry.o: ../src-uland/servers/proc_manager/pm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

vm_entry.o: ../src-lib/libvm/vm_entry.c
	$(CC) -I../tests/include $(CPPFLAGS) $(CFLAGS) -c $< -o $@

mock_vm.o: mock_vm.c
	$(CC) -I../tests/include $(CFLAGS) -c $< -o $@

sched_stub.o: sched_stub.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

test_mailbox.o: test_mailbox.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

test_spinlock.o: test_spinlock.cpp
	$(CXX) $(CXXFLAGS) -I../src-headers -c $< -o $@

test_timer.o: test_timer.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
rm -f $(OBJS) $(MAILBOX_OBJS) $(TIMER_OBJS) \
      test_kern spinlock_cpp mailbox_test timer_test test_spinlock.o

.PHONY: all clean
