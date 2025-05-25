# Third Party Sources

This directory caches source archives and packages used by `setup.sh`.
When run with network access, the script caches clang, cmake and related archives under this directory for offline installs.
Debian packages are looked up under `apt/` and Python wheels under `pip/` when operating offline.
