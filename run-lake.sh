#!/bin/sh
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if [ -n "${ELAN_HOME:-}" ] && [ -x "$ELAN_HOME/bin/lake" ]; then
  export PATH="$ELAN_HOME/bin:$PATH"
elif [ -x "$HOME/.elan/bin/lake" ]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
# Prefer standalone command-line tools when Xcode is not configured on macOS.
if [ "$(uname -s)" = Darwin ] && [ -d /Library/Developer/CommandLineTools ]; then
  export DEVELOPER_DIR=/Library/Developer/CommandLineTools
fi
if ! command -v lake >/dev/null 2>&1; then
  cat >&2 <<'EOF'
Lean's lake command was not found. Install elan, then retry:

  curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path
  export PATH="$HOME/.elan/bin:$PATH"
  ./run-lake.sh --version

If elan is installed in a custom directory, set ELAN_HOME to that directory.
See README.md, "Build and check".
EOF
  exit 127
fi
exec lake "$@"
