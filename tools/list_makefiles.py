#!/usr/bin/env python3
"""List all Makefile paths in the repository."""
import os
import argparse

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

parser = argparse.ArgumentParser(description="Enumerate Makefiles")
parser.add_argument('-o', '--output', help='write list to file')
args = parser.parse_args()

paths = []
for dirpath, dirnames, filenames in os.walk(ROOT):
    if '.git' in dirpath.split(os.sep):
        continue
    for name in filenames:
        if name == 'Makefile':
            rel = os.path.relpath(os.path.join(dirpath, name), ROOT)
            paths.append(rel)

paths.sort()

if args.output:
    with open(args.output, 'w', encoding='utf-8') as f:
        for p in paths:
            f.write(p + '\n')
else:
    for p in paths:
        print(p)
print(f"{len(paths)} Makefiles found")
