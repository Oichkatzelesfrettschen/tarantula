# Offline Packages

Place pre-downloaded `.deb` files in this directory when running `setup.sh --offline`.
Each package should follow the usual `name_version_arch.deb` naming scheme. The script installs these packages with `dpkg -i`.

Populate using:

```sh
apt-get download <pkg>
```

Copy any dependencies as needed. The directory is flat with no subdirectories.
