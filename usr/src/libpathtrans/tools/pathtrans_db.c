#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DEFAULT_DB_FILE "/etc/pathtrans/path_mappings.db"

static const char *get_db_file(void) {
    const char *env = getenv("PATHTRANS_DB");
    return env ? env : DEFAULT_DB_FILE;
}

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s -a <orig> <trans>\n", prog);
}

int main(int argc, char *argv[]) {
    if (argc == 4 && strcmp(argv[1], "-a") == 0) {
        const char *db = get_db_file();
        FILE *f = fopen(db, "a");
        if (!f) {
            perror("open db");
            return 1;
        }
        fprintf(f, "%s %s\n", argv[2], argv[3]);
        fclose(f);
        return 0;
    }

    usage(argv[0]);
    return 1;
}
