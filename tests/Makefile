CC ?= cc
CXX ?= c++
CFLAGS ?= -O2 -pipe -std=c2x -Wall -Wextra -Werror
CXXFLAGS ?= -O2 -pipe -std=c++23 -Wall -Wextra -Werror
CXXFLAGS += -D_Static_assert=static_assert
CPPFLAGS = -I../tests/include -I../src-headers -I../src-headers/machine -I../src-kernel -I../include
LIBS = ../build/libkern_stubs.a ../build/libipc.a ../build/libposix.a
	
OBJS = test_kern.o fs_open.o pm_entry.o vm_entry.o sched_stub.o mock_vm.o
FIFO_OBJS = fifo_test.o
MAILBOX_OBJS = test_mailbox.o
POSIX_SIG_OBJS = modern/posix_signal_demo.o
POSIX_IPC_OBJS = modern/posix_ipc_demo.o

all: test_kern spinlock_cpp mailbox_test fifo_test posix_signal_demo posix_ipc_demo

test_kern: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) $(LIBS) -o $@
	
spinlock_cpp: test_spinlock.o
	$(CXX) $(CXXFLAGS) test_spinlock.o -o $@

mailbox_test: $(MAILBOX_OBJS)
	$(CC) $(CFLAGS) $(MAILBOX_OBJS) $(LIBS) -o $@

fifo_test: $(FIFO_OBJS)
	$(CC) $(CFLAGS) $(FIFO_OBJS) $(LIBS) -o $@

posix_signal_demo: $(POSIX_SIG_OBJS)
	$(CC) $(CFLAGS) $(POSIX_SIG_OBJS) $(LIBS) -o $@

posix_ipc_demo: $(POSIX_IPC_OBJS)
	$(CC) $(CFLAGS) $(POSIX_IPC_OBJS) $(LIBS) -o $@

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

modern/posix_signal_demo.o: modern/posix_signal_demo.c
	$(CC) $(CFLAGS) -c $< -o $@

modern/posix_ipc_demo.o: modern/posix_ipc_demo.c
	$(CC) $(CFLAGS) -c $< -o $@

fifo_test.o: fifo_test.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

test_spinlock.o: test_spinlock.cpp
	$(CXX) $(CXXFLAGS) -I../src-headers -c $< -o $@

clean:
	rm -f $(OBJS) $(MAILBOX_OBJS) $(FIFO_OBJS) $(POSIX_SIG_OBJS) $(POSIX_IPC_OBJS) test_spinlock.o test_kern spinlock_cpp mailbox_test fifo_test posix_signal_demo posix_ipc_demo test_spinlock

.PHONY: all clean
