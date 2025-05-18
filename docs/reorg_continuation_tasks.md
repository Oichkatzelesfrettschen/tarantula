# Directory Restructure and Modernization: Next Steps

This document outlines tasks for agents to continue migrating the 4.4BSD-Lite2 tree to a modern layout while preserving historical context.


## Short-Term Goals

- [ ] **Finalize FHS Mapping**
  - [x] Document any remaining directories that require manual symlink creation
  - [ ] Verify that all top-level directories are mapped to their FHS equivalents
- [ ] **Update Build Scripts**
  - [ ] Adjust makefiles under `usr/src` to reference the new paths created during the migration
  - [x] Ensure `tools/migrate_to_fhs.sh` updates symlinks when rerun
- [ ] **Inventory Remaining Legacy Files**
  - [x] Use `tools/create_inventory.py` to produce an updated file list
  - [ ] Mark files that are deprecated or replaced in the modern layout
## Mid-Term Goals

1. **Library Consolidation**
   - Merge duplicated libraries found in `lib/` and `usr/src/lib`.
   - Create a unified `lib` directory and update dependent makefiles.
2. **Kernel Source Cleanup**
   - Move architecture-specific kernel code under `sys/arch`.
   - Introduce a hardware abstraction layer stub for future expansion.
3. **CI Integration**
   - Expand the existing workflow to test both the historical and restructured layouts.
   - Record build metrics and warnings for each configuration.

## Long-Term Goals

1. **Remove Obsolete Utilities**
   - Identify userland tools superseded by modern counterparts.
   - Provide stubs or compatibility wrappers where required for historical builds.
2. **Update Documentation**
   - Continue updating manuals and README files as directories move.
   - Cross-reference original paths in comments for archival purposes.

These tasks build upon `reorg_plan.md` and `modernization_plan.md`. Agents should update this list as progress is made.
