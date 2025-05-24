# Third Party Sources

This directory caches source archives and packages used by `setup.sh`.
When run with network access, the script fetches the latest `bmake` tarball
from <http://www.crufty.net/ftp/pub/sjg/> and stores it under `bmake/`.
Debian packages are looked up under `apt/` and Python wheels under `pip/`
when operating offline.
