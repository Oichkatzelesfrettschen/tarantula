# Directory Restructure and Modernization: Next Steps

This document outlines tasks for agents to continue migrating the 4.4BSD-Lite2 tree to a modern layout while preserving historical context.


## Short-Term Goals

- [x] **Finalize FHS Mapping**
  - [x] Document any remaining directories that require manual symlink creation
  - [x] Verify that all top-level directories are mapped to their FHS equivalents
- [x] **Update Build Scripts**
  - [x] Adjust makefiles under `usr/src` to reference the new paths created during the migration
  - [x] Ensure `tools/migrate_to_fhs.sh` updates symlinks when rerun
  - The `libpathtrans` library now installs to `src-lib/libpathtrans` and example
    makefiles link against that location.
- [x] **Inventory Remaining Legacy Files**
  - [x] Use `python3 tools/create_inventory.py` to produce an updated file list
 - [x] Mark files that are deprecated or replaced in the modern layout
- [x] **Remove Leftover Object Archives**
  - [x] Purged `.o` and `.a` binaries from `usr/src` and documented the cleanup
## Mid-Term Goals

1. **Library Consolidation**
   - Merge duplicated libraries found in `lib/` and `usr/src/lib`.
   - Create a unified `lib` directory and update dependent makefiles.
2. **Kernel Source Cleanup**
   - Move architecture-specific kernel code under `sys/arch`.
   - Introduce a hardware abstraction layer stub for future expansion.
3. **CI Integration**
   - Reintroduce a CI workflow when needed to test both the historical and restructured layouts.
   - Record build metrics and warnings for each configuration.
4. **Header Tree Unification**
   - Use `tools/sync_sys_headers.sh` to copy kernel headers into `src-headers/sys`.
   - Replace `usr/src/sys/sys` with a symlink pointing at the unified directory.

## Long-Term Goals

1. **Remove Obsolete Utilities**
   - Identify userland tools superseded by modern counterparts.
   - Provide stubs or compatibility wrappers where required for historical builds.
2. **Update Documentation**
   - Continue updating manuals and README files as directories move.
   - Cross-reference original paths in comments for archival purposes.

These tasks build upon `reorg_plan.md` and `modernization_plan.md`. Agents should update this list as progress is made.
