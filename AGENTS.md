# Agent Guide

This repository contains the historical 4.4BSD-Lite2 tree along with modernization notes.
It mirrors a BSD root filesystem layout.

## Key Documentation
- `SOURCE_TREE_OVERVIEW.md` gives a summary of the top-level directories.
- The `docs/` directory holds build instructions and modernization plans.

The optional document `docs/codex_bootstrap.md` explains how to run the
OpenAI Codex CLI at boot so `setup.sh` stays up to date even on hosts that
drop network connectivity shortly after start.

Each major subdirectory includes its own `AGENTS.md` describing that area.

## Workflow Guidelines
- Keep commits focused and update `docs/` when relevant.
- Documentation changes require no automated tests.
- For code changes, try building using the steps in `docs/building_kernel.md`.
