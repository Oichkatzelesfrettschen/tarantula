#include "path_database.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DEFAULT_DB_FILE "/etc/pathtrans/path_mappings.db"

typedef struct {
    char *orig;
    char *trans;
    size_t orig_len;
} mapping_t;

static mapping_t *mappings = NULL;
static size_t mapping_count = 0;
static pthread_rwlock_t db_lock = PTHREAD_RWLOCK_INITIALIZER;

static const char *get_db_file(void) {
    const char *env = getenv("PATHTRANS_DB");
    return env ? env : DEFAULT_DB_FILE;
}

static void free_mappings(void) {
    for (size_t i = 0; i < mapping_count; i++) {
        free(mappings[i].orig);
        free(mappings[i].trans);
    }
    free(mappings);
    mappings = NULL;
    mapping_count = 0;
}

bool reload_path_database(void) {
    const char *db_file = get_db_file();
    FILE *f = fopen(db_file, "r");
    if (!f) {
        return false;
    }

    mapping_t *new_map = NULL;
    size_t count = 0;
    char line[1024];

    while (fgets(line, sizeof(line), f)) {
        if (line[0] == '#' || line[0] == '\n')
            continue;
        char *orig = strtok(line, " \t\n");
        char *trans = strtok(NULL, " \t\n");
        if (!orig || !trans)
            continue;
        mapping_t *tmp = realloc(new_map, (count + 1) * sizeof(mapping_t));
        if (!tmp) {
            fclose(f);
            free_mappings();
            free(new_map);
            return false;
        }
        new_map = tmp;
        new_map[count].orig = strdup(orig);
        new_map[count].trans = strdup(trans);
        new_map[count].orig_len = strlen(orig);
        count++;
    }
    fclose(f);

    pthread_rwlock_wrlock(&db_lock);
    free_mappings();
    mappings = new_map;
    mapping_count = count;
    pthread_rwlock_unlock(&db_lock);
    return true;
}

void path_database_init(void) {
    reload_path_database();
}

void path_database_cleanup(void) {
    pthread_rwlock_wrlock(&db_lock);
    free_mappings();
    pthread_rwlock_unlock(&db_lock);
}

bool path_needs_translation(const char *path) {
    bool result = false;
    pthread_rwlock_rdlock(&db_lock);
    for (size_t i = 0; i < mapping_count; i++) {
        if (strncmp(path, mappings[i].orig, mappings[i].orig_len) == 0) {
            result = true;
            break;
        }
    }
    pthread_rwlock_unlock(&db_lock);
    return result;
}

bool translate_path(const char *orig_path, char *translated_path, size_t size) {
    bool result = false;
    pthread_rwlock_rdlock(&db_lock);
    for (size_t i = 0; i < mapping_count; i++) {
        if (strncmp(orig_path, mappings[i].orig, mappings[i].orig_len) == 0) {
            snprintf(translated_path, size, "%s%s", mappings[i].trans,
                     orig_path + mappings[i].orig_len);
            result = true;
            break;
        }
    }
    pthread_rwlock_unlock(&db_lock);
    return result;
}
