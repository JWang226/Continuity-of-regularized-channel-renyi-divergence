#!/usr/bin/env bash
# Copyright (c) 2026 Jinzhao Wang. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Jinzhao Wang (AI-assisted formalization)

set -euo pipefail
cd "$(dirname "$0")"
mkdir -p .lake
{
  ./run-lake.sh build All ChannelContinuity QuantumChannelContinuity ComparatorChallenges
  ./run-lake.sh env lean Audit.lean
} 2>&1 | tee .lake/check.log
if ! grep -q 'AUDIT PASSED:' .lake/check.log; then
  echo 'Verification failed: audit completion was not recorded.' >&2
  exit 1
fi
