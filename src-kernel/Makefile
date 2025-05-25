OBJS = proc_hooks.o sched_hooks.o vm_hooks.o vfs_hooks.o
LIB = libkern_stubs.a
LIBIPC_DIR = ../src-lib/libipc
LIBIPC = $(LIBIPC_DIR)/libipc.a

CC ?= cc
AR ?= ar
CLANG_TIDY ?= ../tools/run_clang_tidy.sh
CFLAGS ?= -O2 -std=c23 -Wall -Werror
CPPFLAGS += -I../src-headers -I../include


all: $(LIBIPC) $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

$(LIBIPC):
	$(MAKE) -C $(LIBIPC_DIR)

%.o: %.c
	@$(CLANG_TIDY) $< -- $(CC) $(CPPFLAGS) $(CFLAGS) || true
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)
	$(MAKE) -C $(LIBIPC_DIR) clean
	
tidy:
	@for src in $(OBJS:.o=.c); do \
	$(CLANG_TIDY) $$src -- $(CC) $(CPPFLAGS) $(CFLAGS); \
	done
