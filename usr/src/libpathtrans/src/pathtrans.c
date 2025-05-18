#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <fcntl.h>
#include <sys/stat.h>
#include "path_database.h"

static int (*real_open)(const char *, int, ... ) = NULL;
static int (*real_stat)(const char *, struct stat *) = NULL;

static __thread int translation_disabled = 0;

static int is_disabled(void) {
    const char *env = getenv("PATHTRANS_DISABLE");
    return translation_disabled || (env && strcmp(env, "1") == 0);
}

__attribute__((constructor))
static void init(void) {
    real_open = dlsym(RTLD_NEXT, "open");
    real_stat = dlsym(RTLD_NEXT, "stat");
    path_database_init();
}

__attribute__((destructor))
static void fini(void) {
    path_database_cleanup();
}

int open(const char *pathname, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, int);
        va_end(ap);
    }

    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf))) {
            use_path = buf;
        }
    }

    int ret;
    translation_disabled = 1;
    if (flags & O_CREAT)
        ret = real_open(use_path, flags, mode);
    else
        ret = real_open(use_path, flags);
    translation_disabled = 0;
    return ret;
}

int stat(const char *pathname, struct stat *statbuf) {
    const char *use_path = pathname;
    char buf[MAX_PATH_LENGTH];
    if (!is_disabled() && path_needs_translation(pathname)) {
        if (translate_path(pathname, buf, sizeof(buf))) {
            use_path = buf;
        }
    }

    int ret;
    translation_disabled = 1;
    ret = real_stat(use_path, statbuf);
    translation_disabled = 0;
    return ret;
}

