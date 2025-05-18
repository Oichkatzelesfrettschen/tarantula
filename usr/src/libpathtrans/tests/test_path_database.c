#include "../include/path_database.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>

int main(void) {
    char dbtmpl[] = "/tmp/pathtrans_dbXXXXXX";
    int fd = mkstemp(dbtmpl);
    if (fd == -1) {
        perror("mkstemp");
        return 1;
    }
    FILE *f = fdopen(fd, "w");
    if (!f) {
        perror("fdopen");
        close(fd);
        unlink(dbtmpl);
        return 1;
    }
    fprintf(f, "/orig /trans\n");
    fclose(f);

    setenv("PATHTRANS_DB", dbtmpl, 1);
    path_database_init();

    int ret = 0;
    char buf[256];

    if (!path_needs_translation("/orig/file")) {
        fprintf(stderr, "path_needs_translation failed\n");
        ret = 1;
    }

    if (!translate_path("/orig/file", buf, sizeof(buf))) {
        fprintf(stderr, "translate_path failed\n");
        ret = 1;
    } else if (strcmp(buf, "/trans/file") != 0) {
        fprintf(stderr, "unexpected translation: %s\n", buf);
        ret = 1;
    }

    if (path_needs_translation("/other")) {
        fprintf(stderr, "unexpected translation detection\n");
        ret = 1;
    }
    if (translate_path("/other", buf, sizeof(buf))) {
        fprintf(stderr, "unexpected translate success\n");
        ret = 1;
    }

    path_database_cleanup();
    unlink(dbtmpl);
    return ret;
}
