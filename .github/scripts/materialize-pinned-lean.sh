#!/usr/bin/env bash
set -euo pipefail

# Elan's installer sets the default but can leave the toolchain download lazy.
# Resolve transient download failures here, before any dependency/proof command.
for lark_download_attempt in 1 2 3; do
  if "$HOME/.elan/bin/elan" toolchain install leanprover/lean4:v4.19.0; then
    "$HOME/.elan/bin/elan" run leanprover/lean4:v4.19.0 lean --version
    exit 0
  fi
  if [ "$lark_download_attempt" -eq 3 ]; then
    exit 1
  fi
  sleep "$((2 * lark_download_attempt))"
done
