#!/bin/sh
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
exec lake "$@"
