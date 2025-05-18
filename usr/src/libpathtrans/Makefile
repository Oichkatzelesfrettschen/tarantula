CC ?= gcc
# Default compilation flags; callers may append architecture options
# Base flags; caller may append via CFLAGS_EXTRA
CFLAGS ?= -Wall -Wextra -fPIC -O2 -D_GNU_SOURCE
CFLAGS += $(CFLAGS_EXTRA)
# Allow the linker flags to be overridden so `-m32`/`-m64` can be passed
LDFLAGS ?=
LDFLAGS += -shared -ldl -lpthread
INCLUDES = -Iinclude

SRC_DIR = src
BUILD_DIR = build
INCLUDE_DIR = include
TEST_DIR = tests
TOOL_DIR = tools

LIB = libpathtrans.so

SRCS = $(wildcard $(SRC_DIR)/*.c)
OBJS = $(patsubst $(SRC_DIR)/%.c,$(BUILD_DIR)/%.o,$(SRCS))

all: directories $(LIB) tools tests

directories:
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

$(LIB): $(OBJS)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

tools: $(LIB)
	$(MAKE) -C $(TOOL_DIR)

tests: $(LIB)
	$(MAKE) -C $(TEST_DIR)

clean:
	rm -rf $(BUILD_DIR) $(LIB)
	$(MAKE) -C $(TOOL_DIR) clean
	$(MAKE) -C $(TEST_DIR) clean

install: $(LIB)
	mkdir -p $(DESTDIR)/usr/lib
	mkdir -p $(DESTDIR)/usr/bin
	mkdir -p $(DESTDIR)/etc/pathtrans
	install -m 755 $(LIB) $(DESTDIR)/usr/lib/
	install -m 755 $(TOOL_DIR)/pathtrans_db $(DESTDIR)/usr/bin/
	install -m 644 config/config.conf $(DESTDIR)/etc/pathtrans/

.PHONY: all directories tools tests clean install
