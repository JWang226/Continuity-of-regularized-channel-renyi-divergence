<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->

# Elaboration before/after — 2026-10-06

Before: `03dde86daf40a3752c273a3017399539e5c7def9` after the dead-code sweep. After: `8765c21753175381a57b29fa9469b35675515b2c` after the measured elaboration cleanup. These are separate source snapshots; no numbers below substitute for proof validation.

The filename date `2026-10-06` is the campaign label. Authoritative UTC windows: before `2026-10-06T22:42:09.071683+00:00` to `2026-10-06T23:09:05.342587+00:00`; after `2026-10-07T00:26:37.635181+00:00` to `2026-10-07T00:53:57.254527+00:00`.

| Metric | Before | After | Δ | Relative Δ |
| --- | --- | --- | --- | --- |
| Wall (s) | 1,586.74 | 1,616.34 | +29.60 | +1.9% |
| User CPU (s) | 1,033.04 | 1,076.03 | +42.99 | +4.2% |
| System CPU (s) | 1,024.18 | 895.05 | -129.13 | -12.6% |
| Measured CPU: user + system (s) | 2,057.22 | 1,971.08 | -86.14 | -4.2% |
| Peak accounted RSS (KiB) | 2,615,936 | 3,116,208 | +500,272 | +19.1% |
| Peak accounted RSS (GiB) | 2.495 | 2.972 | +0.477 | +19.1% |
| Summed Built elapsed durations (s; NOT CPU) | 7,832.00 | 6,706.00 | -1,126.00 | -14.4% |
| Logged implied parallelism | 4.94 | 4.15 | -0.79 | -15.9% |
| Logged elapsed ms / code line | 894.17 | 764.65 | -129.51 | -14.5% |
| Compiled own modules | 83.00 | 83.00 | +0.00 | +0.0% |

## Comparability and limits

Execution script SHAs differ only by the independently checked one-line intentional-sorry warning parser correction. Original execution SHA/timing and false-invalid baseline result are preserved; the saved raw log was reclassified without retiming. This is a documented analysis correction, not silently identical instrumentation. Logged implied parallelism differs by more than the report's 10% descriptive tolerance; no wall-speedup claim. Contention indicators detected: same-file logged times moved both up and down by more than 10%. Co-running Lean/Lake commands were observed. Presence alone neither invalidates the run nor proves contamination; actual source/dependency mutation guards determine validity.

The 10% parallelism tolerance is a declared descriptive reporting rule, not an upstream statistical guarantee. Raw wall differences are displayed even when the gate rejects a speedup conclusion. Logged durations are per-module elapsed values; GNU time measures process CPU separately. Each committed input is SHA-bound and checked against Git.

The summed Built elapsed change (**-14.38%**) is not a project-speedup percentage: these overlapping per-module durations are not total CPU or wall time. Logged implied parallelism changed **-15.94%**; it is outside the matched 10% range, so whole-build wall-speedup claims are rejected. User CPU changed **+4.16%** while system CPU changed **-12.61%**. The aggregate CPU difference does not isolate proof search. Peak accounted RSS changed **+19.12%**; this is a measured maximum process/child RSS observation, not concurrent-worker memory summed together, and no stable memory-improvement or no-regression claim follows.

## Warm profiles, matched files

| File | Before wall | After wall | Δ wall | Before import | After import | Δ import |
| --- | --- | --- | --- | --- | --- | --- |
| `QuantumChannelContinuity/Filter.lean` | 49.08 | 40.25 | -8.83 | 36.00 | 21.20 | -14.80 |
| `QuantumChannelContinuity/FilterAlignment.lean` | 69.29 | 51.84 | -17.45 | 53.30 | 39.00 | -14.30 |
| `QuantumChannelContinuity/OrderConvexity.lean` | 36.67 | 22.18 | -14.49 | 28.70 | 13.00 | -15.70 |
| `QuantumChannelContinuity/RegularizationSup.lean` | 116.86 | 15.42 | -101.44 | 103.00 | 7.15 | -95.85 |
| `QuantumChannelContinuity/SDPCone.lean` | 112.79 | 87.87 | -24.92 | 58.00 | 55.20 | -2.80 |
| `QuantumChannelContinuity/SDPTrace.lean` | 95.18 | 53.93 | -41.25 | 52.50 | 40.70 | -11.80 |
| `QuantumChannelContinuity/Schatten.lean` | 65.56 | 86.64 | +21.08 | 40.10 | 53.80 | +13.70 |
| `QuantumChannelContinuity/SourceCorrespondence.lean` | 39.58 | 40.08 | +0.50 | 31.90 | 29.70 | -2.20 |
| `QuantumChannelContinuity/TensorChannels.lean` | 48.48 | 61.32 | +12.84 | 23.10 | 47.80 | +24.70 |

| File | Before typeclass (s) | After typeclass (s) | Δ typeclass (s) |
| --- | --- | --- | --- |
| `QuantumChannelContinuity/Filter.lean` | 19.50 | 20.70 | +1.20 |
| `QuantumChannelContinuity/FilterAlignment.lean` | 9.67 | 6.06 | -3.61 |
| `QuantumChannelContinuity/OrderConvexity.lean` | 0.29 | 0.22 | -0.07 |
| `QuantumChannelContinuity/RegularizationSup.lean` | 1.06 | 0.20 | -0.86 |
| `QuantumChannelContinuity/SDPCone.lean` | 47.20 | 24.40 | -22.80 |
| `QuantumChannelContinuity/SDPTrace.lean` | 40.20 | 6.82 | -33.38 |
| `QuantumChannelContinuity/Schatten.lean` | 55.70 | 101.00 | +45.30 |
| `QuantumChannelContinuity/SourceCorrespondence.lean` | 1.23 | 2.83 | +1.60 |
| `QuantumChannelContinuity/TensorChannels.lean` | 14.50 | 6.64 | -7.86 |

Compare both increases and decreases in these typeclass elapsed counters. These observations neither establish stable effects nor isolate proof-search CPU or the cause of an increase. The single-intervention screens and their retained/reverted decisions are reported separately.

Warm commands run serially, but Lean itself can execute tasks in parallel and single per-file samples still contain noise. Retained-intervention A/B repetitions, if any, are documented separately below. Flat `--profile` component counters are exclusive within instrumented stacks; aggregation across threads/tasks can exceed wall time. They do not partition the wall clock, and their sum is not GNU process CPU/wall time. Structured nested profiler traces are separate and may contain overlapping durations as well.

## Heavy-tail policy metric

| Tier | Before | After | Δ |
| --- | --- | --- | --- |
| ≥10 s | 83 | 83 | +0 |
| ≥20 s | 83 | 78 | -5 |
| ≥30 s | 83 | 76 | -7 |
| ≥40 s | 83 | 67 | -16 |

## Measured interventions

Ranked by actionability: retained trace-supported closed-head caches first, retained import reductions next by measured phase decrease, other candidates next, rejected probes last. The retained import order uses **one A/B sample per state**, not a statistical ranking of stable speedups. A named trace mechanism supports the cache diagnosis without attributing whole-build changes to it.

1. **Cache the canonical real Module instance for Hermitian operators in the trace-duality provider** — lever: one trace-confirmed closed head-class cache; status: retained.


```json
{
  "file": "QuantumChannelContinuity/SDPTrace.lean",
  "trace_probe_sha256": "959c2943055c01ca5c95a31febc4bac1a271512bc630270176be223bdd2aec1d",
  "trace_log_sha256": "a045703c0b58d5ce3068d54e853cd8062553807488bf97b9cd1d5689d12ea9d4",
  "trace_diagnosis": "Eight closed Module real Hermitian goals; seven fresh repeated resolutions, one internal cached result. No derived/open-head caches.",
  "before_typeclass_seconds": 29.1,
  "before_wall_seconds": 87.05,
  "baseline_source_sha256": "42376ffe8705eb9591d75e599c87060502b2763c824dcb6c84020346579e48bb",
  "evidence_before": "docs/elaboration/ab/ab-hermitian-module-before/profiles.json",
  "timing_claim": "Single untraced serial sample per state; no robust wall-speedup claim.",
  "after_typeclass_seconds": 10.8,
  "delta_typeclass_seconds": -18.3,
  "phase_threshold_passed": true,
  "other_profiler_elapsed_before": 14.53815,
  "other_profiler_elapsed_after": 5.93693,
  "other_phase_regression_screen": false,
  "variant_source_sha256": "2a9a58e75c92968a666b8e890e88e031baf8f14885ee51c010a36c90c2b26f84",
  "after_wall_seconds": 36.19,
  "evidence_after": "docs/elaboration/ab/ab-hermitian-module-after/profiles.json",
  "commit": "8e0aba7c3894fb4c9a4ea428db7fc4ebe4b7238a",
  "propagation": {
    "consumer": "QuantumChannelContinuity/SDPCone.lean",
    "before_typeclass_seconds": 143.0,
    "after_typeclass_seconds": 61.1,
    "delta_seconds": -81.9,
    "passes_half_second_screen": true,
    "control_source_commit": "7378ca17124344ff52630bbeb7083ab5f7256301",
    "variant_source_commit": "8e0aba7c3894fb4c9a4ea428db7fc4ebe4b7238a",
    "provider_olean_before_sha256": "186be537f6f19c38cc39753985e9933c948a3c4652946f8b020dd7a906bc9fa0",
    "provider_olean_after_sha256": "18dcd45c5171bbd36c34564a3d1c6cad528ed423fdc00e40b534ac24a6c6f2e5",
    "method": "Fresh consumer control with original provider source/artifact, then rebuild only the retained provider via run-lake env lean -o. Other own/imported artifacts unchanged. Source restored in finally; full Lake rebuild follows.",
    "provider_build_exit_code": 0,
    "dependency_artifacts_unchanged": true,
    "provider_rebuild_log_sha256": "90c30643db0bd7f4951fa6f470ed053a646622865750f14426e1d94cd4107a67",
    "evidence_before": "docs/elaboration/ab/ab-hermitian-propagation-before/profiles.json",
    "evidence_after": "docs/elaboration/ab/ab-hermitian-propagation-after/profiles.json"
  },
  "trace_evidence": "docs/elaboration/trace/manifest.json"
}
```

The provider's warm A/B peak accounted RSS rose from **2,008,880 to 2,565,536 KiB** (+27.7%). This is a memory observation from one pair; the phase screen does not establish a stable global memory improvement or attribute this rise to the cache alone.

2. **Narrow consumer imports in QuantumChannelContinuity/RegularizationSup.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "QuantumChannelContinuity/RegularizationSup.lean",
  "baseline_source_sha256": "e5bba3db0c8dc9d2923a340f0dd7fce2b5c87c53fc925bfe07eae518f7d7c450",
  "variant_source_sha256": "7dbe59ae3c10cea71fba827bd40fb016ef2b0eb00b98c865a55bf24d24d2dbbf",
  "phase": "import",
  "before_seconds": 85.4,
  "after_seconds": 12.5,
  "delta_seconds": -72.9,
  "nonimport_profiler_elapsed_before": 7.192328,
  "nonimport_profiler_elapsed_after": 2.4333343000000003,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 96.53,
  "after_wall_seconds": 21.94,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [],
  "evidence_before": "docs/elaboration/ab/ab-regularization-sup-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-regularization-sup-after/profiles.json",
  "commit": "090b56d77a67e4de1c6ccce3751155e932eafbdb"
}
```

3. **Narrow consumer imports in ChannelContinuity/LeftContinuity.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "ChannelContinuity/LeftContinuity.lean",
  "baseline_source_sha256": "5455416ecccc5f5545ce7eaf9abefb31f00b8767c5a0965203ff7d619efcfce9",
  "variant_source_sha256": "4af1cff964375e77c8b8050819ea5dcbc64a0f8247e4228f0ee0b59ba734e8ff",
  "phase": "import",
  "before_seconds": 94.5,
  "after_seconds": 31.2,
  "delta_seconds": -63.3,
  "nonimport_profiler_elapsed_before": 7.387899,
  "nonimport_profiler_elapsed_after": 3.8905,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 107.63,
  "after_wall_seconds": 40.4,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [],
  "evidence_before": "docs/elaboration/ab/ab-left-continuity-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-left-continuity-after/profiles.json",
  "commit": "425ec25366a806771875c28c2d588c7305ad3954"
}
```

4. **Narrow consumer imports in QuantumChannelContinuity/OrderConvexity.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "QuantumChannelContinuity/OrderConvexity.lean",
  "baseline_source_sha256": "fb94c303540e604639a0e0ac2c0f3c627c0d1ff072d91567be059828be197afb",
  "variant_source_sha256": "cc10d02a4608b1c890051575961d53818de5a6e4521a6f5585186811e64de935",
  "phase": "import",
  "before_seconds": 58.8,
  "after_seconds": 8.98,
  "delta_seconds": -49.81999999999999,
  "nonimport_profiler_elapsed_before": 5.739703,
  "nonimport_profiler_elapsed_after": 2.413661,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 68.48,
  "after_wall_seconds": 15.83,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [],
  "evidence_before": "docs/elaboration/ab/ab-order-convexity-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-order-convexity-after/profiles.json",
  "initial_provider_probe": {
    "status": "failed then restored",
    "exit_code": 1,
    "reason": "Missing Real notation and instances; corrected variant explicitly imports Mathlib.Data.Real.Basic",
    "evidence": "docs/elaboration/ab/ab-order-convexity-provider-failure/profiles.json"
  },
  "commit": "25324aace674a74097cfc06fac08488a8c85298a"
}
```

5. **Narrow consumer imports in QuantumChannelContinuity/Filter.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "QuantumChannelContinuity/Filter.lean",
  "baseline_source_sha256": "fb391a13524509379adc5bc8aa80bf846155f2d76cdbaaf028ec6d857f742da2",
  "variant_source_sha256": "b2ee2c121040b52b943264d6263117447bf672dfb1de6da4516668754ff395c5",
  "phase": "import",
  "before_seconds": 106.0,
  "after_seconds": 56.2,
  "delta_seconds": -49.8,
  "nonimport_profiler_elapsed_before": 59.127404,
  "nonimport_profiler_elapsed_after": 45.21687,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 135.87,
  "after_wall_seconds": 79.34,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [],
  "evidence_before": "docs/elaboration/ab/ab-filter-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-filter-after/profiles.json",
  "commit": "3a9e14a21d7542ae8edb7aebdf683faf5b9068d3"
}
```

6. **Narrow consumer imports in ChannelContinuity/ThreePiece.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "ChannelContinuity/ThreePiece.lean",
  "baseline_source_sha256": "efe31b5a7a48261890f7a12835662d8b508e7216676fa62857795181eaef6680",
  "variant_source_sha256": "3e940b2ff026525195827afdff2eec08c8bccd6161c39e3630866b51ce3d6468",
  "phase": "import",
  "before_seconds": 52.3,
  "after_seconds": 6.95,
  "delta_seconds": -45.349999999999994,
  "nonimport_profiler_elapsed_before": 6.0546421,
  "nonimport_profiler_elapsed_after": 2.1855564000000003,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 65.14,
  "after_wall_seconds": 13.66,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [
    "ChannelContinuity/Parameters.lean"
  ],
  "evidence_before": "docs/elaboration/ab/ab-three-piece-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-three-piece-after/profiles.json",
  "commit": "87a4839315fcc70faef853fb84041ff2669c0cfc"
}
```

7. **Narrow consumer imports in ChannelContinuity/Threshold.lean** — lever: consumer import narrowing; status: retained.


```json
{
  "file": "ChannelContinuity/Threshold.lean",
  "baseline_source_sha256": "b931b8ddf3ec65c6c2223beaaf868dd795a43aa156da6ec44c0660a327a60a3c",
  "variant_source_sha256": "e1b599deba5746c126125cd9cf1dc024b22d75d4a03840b4a9e7377c2bd930e2",
  "phase": "import",
  "before_seconds": 42.6,
  "after_seconds": 16.8,
  "delta_seconds": -25.8,
  "nonimport_profiler_elapsed_before": 5.54388,
  "nonimport_profiler_elapsed_after": 5.285272,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": false,
  "before_wall_seconds": 50.66,
  "after_wall_seconds": 25.19,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [
    "ChannelContinuity/Main.lean"
  ],
  "evidence_before": "docs/elaboration/ab/ab-threshold-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-threshold-after/profiles.json",
  "commit": "7378ca17124344ff52630bbeb7083ab5f7256301"
}
```

8. **Narrow consumer imports in QuantumChannelContinuity/Schatten.lean** — lever: consumer import narrowing; status: reverted.


```json
{
  "file": "QuantumChannelContinuity/Schatten.lean",
  "baseline_source_sha256": "15b6bfdfbfea1da59b25aeb2915780a6955a1907175231ab0611d379cce48675",
  "variant_source_sha256": "c6ea5c22dfede1809ac866258c6b2bdbd2ab30ec1b3b113d59e8b96f98b3a159",
  "phase": "import",
  "before_seconds": 93.1,
  "after_seconds": 92.8,
  "delta_seconds": -0.29999999999999716,
  "nonimport_profiler_elapsed_before": 130.86974,
  "nonimport_profiler_elapsed_after": 162.700148,
  "phase_threshold_passed": false,
  "other_phase_regression_screen": true,
  "before_wall_seconds": 131.26,
  "after_wall_seconds": 136.96,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [],
  "evidence_before": "docs/elaboration/ab/ab-schatten-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-schatten-after/profiles.json"
}
```

9. **Narrow consumer imports in ChannelContinuity/Limsup.lean** — lever: consumer import narrowing; status: reverted.


```json
{
  "file": "ChannelContinuity/Limsup.lean",
  "baseline_source_sha256": "ddddd0a5409956d0f2894390b261ebffdc2bcc2edb669e043941c07dc139d9aa",
  "variant_source_sha256": "6b18d4ab1bec4c552f0279dfd6c9d091822abd7881e03a398af5f79344a87cb2",
  "phase": "import",
  "before_seconds": 67.2,
  "after_seconds": 23.2,
  "delta_seconds": -44.0,
  "nonimport_profiler_elapsed_before": 2.8958757,
  "nonimport_profiler_elapsed_after": 4.993692500000001,
  "phase_threshold_passed": true,
  "other_phase_regression_screen": true,
  "before_wall_seconds": 74.52,
  "after_wall_seconds": 32.36,
  "timing_claim": "One serial sample per state; host load varies. No robust wall-speedup conclusion. Flat elapsed counters overlap across threads.",
  "required_provider_adjustments": [
    "ChannelContinuity/Limsup.lean"
  ],
  "evidence_before": "docs/elaboration/ab/ab-limsup-before/profiles.json",
  "evidence_after": "docs/elaboration/ab/ab-limsup-after/profiles.json"
}
```

## Evidence and full reports

- [Before report](../../ELABORATION_REPORT_2026-10-06_BEFORE.md)
- [After report](../../ELABORATION_REPORT_2026-10-06_AFTER.md)
- [Reproduction guide](README.md)
