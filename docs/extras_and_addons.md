# Extras and Add-ons Overview

This note summarizes additional material in the repository beyond the historical 4.4BSD-Lite2 sources. These extras aid modernization and experimentation.

## Experimental Ports

Under `ports/` the tree provides language ports used for prototyping:

- `ports/chicken/` – minimal utilities written in Chicken Scheme.
- `ports/go/` – Go implementations of selected tools.

Each subdirectory is self-contained with its own README and build steps.

## Numbered Manual Pages

The `usr/share/man` hierarchy includes preformatted manual pages stored with numbered extensions such as `hangman.0` and `diff3.0`. These files mirror the historic `cat?` directories from the BSD distributions. The numbers correspond to the manual section. For example:

```
usr/share/man/cat6/hangman.0   # section 6 games manual
usr/share/man/cat1/diff3.0     # section 1 general commands
```

These names remain unchanged to preserve the original distribution layout. When migrating to an FHS structure the files can be placed under `/usr/share/man/cat?` with identical names.

## Offline Packages and Third-Party Sources

The repository contains an `offline_packages/` directory for stashing pre-downloaded `.deb` packages. Install them manually with `dpkg -i` when the network is unavailable. Python wheels cached under `third_party/pip/` and Debian packages in `third_party/apt/` are also checked before contacting the network.

## Migration Helpers

Two primary scripts automate directory reorganization:

- `tools/migrate_to_fhs.sh` – copies legacy directories under `/usr` and creates symlinks for a hybrid FHS layout.
- `tools/migrate_to_src_layout.sh` – relocates sources into `src-kernel`, `src-uland`, `src-lib` and `src-headers`.

Run them sequentially inside a chroot to modernize the tree while preserving compatibility links.

