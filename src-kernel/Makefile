
OBJS = proc_hooks.o sched_hooks.o vm_hooks.o vfs_hooks.o ipc.o
LIB = libkern_stubs.a

CC ?= cc
AR ?= ar
CLANG_TIDY ?= ../tools/run_clang_tidy.sh
CFLAGS ?= -O2 -std=c2x
CPPFLAGS += -I../include


all: $(LIB)

$(LIB): $(OBJS)
	$(AR) rcs $@ $(OBJS)

%.o: %.c
	@$(CLANG_TIDY) $< -- $(CC) $(CPPFLAGS) $(CFLAGS) || true
	$(CC) $(CPPFLAGS) $(CFLAGS) -c $< -o $@

clean:
	rm -f $(OBJS) $(LIB)
	
tidy:
	@for src in $(OBJS:.o=.c); do \
	$(CLANG_TIDY) $$src -- $(CC) $(CPPFLAGS) $(CFLAGS); \
	done
