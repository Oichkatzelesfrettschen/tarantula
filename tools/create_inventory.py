#!/usr/bin/env python3
"""Generate a list of all files in the repository.

The output is written to docs/file_inventory.txt. Paths are relative to the
repository root and sorted alphabetically.
"""

import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUTPUT = os.path.join(ROOT, 'docs', 'file_inventory.txt')

paths = []
for dirpath, dirnames, filenames in os.walk(ROOT):
    # skip .git directory
    if '.git' in dirpath.split(os.sep):
        continue
    for name in filenames:
        rel = os.path.relpath(os.path.join(dirpath, name), ROOT)
        paths.append(rel)

with open(OUTPUT, 'w', encoding='utf-8') as f:
    for p in sorted(paths):
        f.write(p + '\n')

print(f"Wrote {len(paths)} paths to {OUTPUT}")
