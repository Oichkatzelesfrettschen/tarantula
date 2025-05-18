#ifndef PATH_DATABASE_H
#define PATH_DATABASE_H

#include <stdbool.h>
#include <stddef.h>

#define MAX_PATH_LENGTH 4096

/* Database operations */
void path_database_init(void);
void path_database_cleanup(void);
bool translate_path(const char *original_path, char *translated_path, size_t translated_path_size);
bool path_needs_translation(const char *path);
bool reload_path_database(void);

#endif /* PATH_DATABASE_H */
