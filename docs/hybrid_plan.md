# Hybrid FHS/Legacy Layout Plan

This short note explains the "hybrid" source tree model used after the initial
[FHS migration](fhs_migration.md). The goal is to keep compatibility with
historic paths while still adopting a more conventional `/usr/src` layout.

## Motivation

Some build scripts expect the traditional BSD hierarchy with `bin`, `sbin` and
other directories at the root. Others work best when headers and sources live
under `/usr/src` in an FHS-style structure. The hybrid model preserves the root
symlinks created by `migrate_to_fhs.sh` but moves active development into the
`src-*` directories.

## Workflow

1. Run `tools/migrate_to_fhs.sh` inside a chroot (use `--force` otherwise) to
   populate `/usr` and create compatibility symlinks.
2. Immediately follow with `tools/migrate_to_src_layout.sh` to relocate the
   kernel, userland and libraries under `src-kernel`, `src-uland` and `src-lib`.
   This script supersedes the older `tools/organize_sources.sh` helper.
3. Update build scripts as described in [reorg_plan.md](reorg_plan.md) so that
   new code references the `src-*` paths while legacy targets continue to work
   via symlinks.

With this approach the repository works as a bridge between the historical
layout and a modern source tree.
