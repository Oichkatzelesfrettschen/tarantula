# Offline Packages

Place pre-downloaded `.deb` files in this directory when preparing for offline
installs. Each package should follow the usual `name_version_arch.deb` naming
scheme. Install them manually with `dpkg -i`.

Populate using:

```sh
apt-get download <pkg>
```

Copy any dependencies as needed. The directory is flat with no subdirectories.
