#!/bin/sh
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if ! command -v python3 >/dev/null 2>&1; then
  echo 'Python 3.9 or newer is required to run the Nanoda reproducer.' >&2
  exit 127
fi
exec python3 scripts/check-nanoda.py "$@"
