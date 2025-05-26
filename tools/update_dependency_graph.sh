#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

python3 "$SCRIPT_DIR/generate_dependency_graph.py" "$@"
mv dependency_graph.dot "$REPO_ROOT/docs/dependency_graph.dot"
echo "Updated docs/dependency_graph.dot"

