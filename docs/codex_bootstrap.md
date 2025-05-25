# Codex Bootstrapping and Offline Setup

This repository can be used with the OpenAI Codex CLI to keep `setup.sh` in sync and to fetch packages before network access disappears. The common workflow is:

1. **Install Codex CLI** – `npm i -g @openai/codex` or include it in your devcontainer.
2. **Automate setup.sh** – Codex checks `setup.sh` against a template and patches any drift. Run:
   ```sh
   codex -q -a full-auto "doctor setup.sh"
   ```
   before executing the script. The wrapper `.codex/setup.sh` does this automatically when run inside CI.
3. **Run during boot** – A sample systemd unit file lives at `etc/systemd/system/codex-setup.service`. Enabling it ensures Codex repairs `setup.sh` and launches it before `network-pre.target` so the script can still download packages.

The service is enabled with:

```sh
sudo systemctl daemon-reload
sudo systemctl enable codex-setup.service
```

After a reboot you can inspect `/var/log/syslog` or use `journalctl -b -u codex-setup` to verify that Codex ran.

Offline runs place pre-downloaded `.deb` files under `offline_packages/` and Python wheels under `third_party/pip/`. Invoke `setup.sh --offline` when the network is not available. Codex detects network access automatically when called via `.codex/setup.sh`.
