# Tooling Progress Report

This document records the current presence of build and documentation tooling within the repository. The survey was performed after provisioning the necessary packages via `apt` and `pip`.

## Environment Setup
- `apt-get update`
- `apt-get install -y cmake doxygen python3-sphinx mandoc cscope bmake universal-ctags`
- `pip install --user cmake sphinx pre-commit`

## Tool Locations
`which` verified the installation paths of key binaries:

- `cmake` – `/usr/bin/cmake`
- `doxygen` – `/usr/bin/doxygen`
- `sphinx-build` – `/usr/bin/sphinx-build`
- `mandoc` – `/usr/bin/mandoc`
- `cscope` – `/usr/bin/cscope`
- `bmake` – `/usr/bin/bmake`
- `ctags` – `/usr/bin/ctags`
- `pre-commit` – `/root/.local/bin/pre-commit`

## CMake
`cmake` resides at `/usr/bin/cmake`.

```
$ cmake --version
cmake version 3.28.3
CMake suite maintained and supported by Kitware (kitware.com/cmake).
```

The following CMake configuration files were located:

```
./CMakeLists.txt
./src-uland/servers/proc_manager/CMakeLists.txt
./src-uland/servers/reincarnation/CMakeLists.txt
```

Directories not listed above currently lack `CMakeLists.txt` files.

## Doxygen
`doxygen` resides at `/usr/bin/doxygen`.

```
$ doxygen --version
1.9.8
```

Doxygen configuration detected at:

```
./docs/Doxyfile
```

No additional `Doxyfile` instances were found.

## Sphinx
`sphinx-build` resides at `/usr/bin/sphinx-build`.

```
$ sphinx-build --version
sphinx-build 7.2.6
```

No `conf.py` files were discovered; Sphinx documentation has not yet been configured within the repository.

## Mandoc
`mandoc` resides at `/usr/bin/mandoc`. Rendering a sample page verifies functionality:

```
$ mandoc Domestic/src/bdes/bdes.1 | head -n 5
BDES(1)                     General Commands Manual                    BDES(1)

NAME
       bdes - encrypt/decrypt using the Data Encryption Standard
```

### Inventory summary
A repository-wide search located 1,176 manual pages.
Distribution by section:

| Section | Count |
| ------- | ----- |
| 1 | 311 |
| 2 | 119 |
| 3 | 299 |
| 4 | 137 |
| 5 | 68 |
| 6 | 46 |
| 7 | 17 |
| 8 | 179 |

Most pages reside under `usr/src` (1,173 files); `Domestic` and `Foreign` contribute only three pages combined. Within `usr/src`, the densest subtrees are `lib` (376 files), `contrib` (207), `share` (182), and `usr.bin` (177).

An alphabetically sorted inventory is stored in [`docs/mandoc_inventory.txt`](mandoc_inventory.txt). The first few entries are:

```
./Domestic/src/bdes/bdes.1
./Domestic/src/libc/crypt.3
./Foreign/src/libc/crypt.3
./usr/src/bin/cat/cat.1
./usr/src/bin/chmod/chmod.1
```

## ctags
`ctags` is available at `/usr/bin/ctags`.

```
$ ctags --version
Universal Ctags 5.9.0, Copyright (C) 2015 Universal Ctags Team
Universal Ctags is derived from Exuberant Ctags.
Exuberant Ctags 5.8, Copyright (C) 1996-2009 Darren Hiebert
  Compiled: Sep  3 2021, 18:12:18
  URL: https://ctags.io/
  Optional compiled features: +wildcards, +regex, +gnulib_regex, +iconv, +option-directory, +xpath, +json, +interactive, +sandbox, +yaml, +packcc, +optscript
```

Running `ctags -R --fields=+l --extras=+q` emitted warnings for missing historical paths, for example:

```
ctags: Warning: cannot open input file "usr/src/sys/tahoe/vba/tags" : No such file or directory
ctags: Warning: cannot open input file "usr/src/sys/tahoe/if/tags" : No such file or directory
ctags: Warning: cannot open input file "usr/src/sys/tahoe/tahoe/tags" : No such file or directory
ctags: Warning: cannot open input file "usr/src/sys/tahoe/include/tags" : No such file or directory
ctags: Warning: cannot open input file "usr/src/sys/luna68k/conf/tags" : No such file or directory
```

The generated `tags` index was removed afterward to keep the repository tidy.

## cscope
`cscope` resides at `/usr/bin/cscope`.

```
$ cscope -V
cscope: version 15.9
```

Executing `cscope -b -R` produced a 51 MB cross-reference database:

```
-rw-r--r-- 1 root root 51M Aug 11 22:21 cscope.out
```

The file was deleted afterward to preserve a clean working tree.

## bmake
`bmake` resides at `/usr/bin/bmake` and reports version:

```
$ bmake -V MAKE_VERSION
20200710
```

Attempting a top-level install within `usr/src` produced no target:

```
$ (cd usr/src && bmake -n install)
bmake: don't know how to make install. Stop
bmake: stopped in /workspace/tarantula/usr/src
```

Running the same command in `usr/src/share/mk` encountered legacy syntax:

```
$ (cd usr/src/share/mk && bmake -n install)
bmake: "/workspace/tarantula/usr/src/share/mk/bsd.prog.mk" line 166: if-less endif
bmake: Fatal errors encountered -- cannot continue
bmake: stopped in /workspace/tarantula/usr/src/share/mk
```

## pre-commit
`pre-commit` is installed at `/root/.local/bin/pre-commit`.

```
$ pre-commit --version
pre-commit 4.3.0
```

Invoking `pre-commit run --files docs/tooling_progress.md` attempted to fetch hooks and prompted for GitHub credentials:

```
Username for 'https://github.com':
[INFO] Initializing environment for https://github.com/pre-commit/mirrors-clang-format.
[INFO] Initializing environment for https://github.com/pre-commit/mirrors-clang-tidy.
Interrupted (^C): KeyboardInterrupt:
```

