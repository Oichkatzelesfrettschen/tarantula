# Third Party Sources

This directory caches upstream source archives downloaded by `setup.sh`.
When run with network access, the script fetches the latest `bmake` tarball
from <http://www.crufty.net/ftp/pub/sjg/> and stores it under `bmake/`.
If offline, the script reuses whichever tarball already exists here.
