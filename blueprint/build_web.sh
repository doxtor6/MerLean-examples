#!/bin/bash
# Build leanblueprint web with UTF-8 encoding support
# Cross-platform (Linux, macOS)

# Force UTF-8 encoding
export PYTHONIOENCODING=utf-8
export PYTHONUTF8=1
export LC_ALL=C.UTF-8
export LANG=C.UTF-8

# Change to blueprint directory
cd "$(dirname "$0")"

echo "Building leanblueprint web with UTF-8 encoding..."
leanblueprint web
