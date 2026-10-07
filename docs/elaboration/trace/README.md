<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->

# Closed instance-search diagnostic

The retained probe is the original `SDPTrace` declaration prefix, with `trace.Meta.synthInstance` enabled. It exposed seven fresh resolutions of the closed goal `Module ℝ (Hermitian H)` and one internal cached result. This justified screening one canonical Module cache. No cache was added for open goals or already cached derived searches.

The trace is diagnostic evidence; it is not a timing result or certification. The separate untraced A/B profiles and provider-propagation test supply the retention screen. See [the intervention record](../interventions.json).

After preparing the pinned dependency and project artifacts, reproduce from the repository root:

```sh
mkdir -p .lake/elaboration/probes
cp docs/elaboration/trace/SDPTraceInstances.probe.txt .lake/elaboration/probes/replay.lean
./run-lake.sh env lean .lake/elaboration/probes/replay.lean > .lake/elaboration/probes/replay.txt 2>&1
```

The probe deliberately retains the pre-cache prefix even in a current checkout. Hashes and the original guard outcomes are in [manifest.json](manifest.json) and [result.json](result.json). Tracing overhead and host load make its elapsed time unsuitable for A/B comparison.
