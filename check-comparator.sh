#!/bin/sh
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo 'Python 3.9 or newer is required to run the Comparator reproducer.' >&2
  exit 127
fi
exec python3 scripts/check-comparator.py "$@"
