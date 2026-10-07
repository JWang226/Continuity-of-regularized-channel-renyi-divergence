<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->

# Elaboration report — 2026-10-06 — BEFORE

## 1. Setup and provenance

Measured commit: `03dde86daf40a3752c273a3017399539e5c7def9`. UTC window: `2026-10-06T22:42:09.071683+00:00` to `2026-10-06T23:09:05.342587+00:00`. Host: `macOS-27.2-arm64-arm-64bit-Mach-O`; reported logical cores: 8. Lean: `Lean (version 4.29.0-rc6, arm64-apple-darwin24.6.0, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release)`.

The report/filename date `2026-10-06` labels the cleanup campaign, not necessarily this run's UTC date. The recorded measurement UTC timestamps are authoritative.

Timing tool: `time (GNU Time) 1.10` using `-v`. Scheduling: Lake default; no explicit concurrency override. Explicit targets: `All, ChannelContinuity, QuantumChannelContinuity, ComparatorChallenges`. These targets cover the committed facade import closure plus Comparator specifications/controls. Lake's default library globs select root modules, not every submodule. The timed scope is 83 owned modules; the supplementary `SourceCorrespondence` module is outside that cold-build closure.

Only the checkout's resolved `.lake/build` was invalidated after rejecting symlinks or dependency caches nested in that subtree. Dependencies remained inputs. No `lake clean` or `lake update` is part of this measurement.

Observed Lean/Lake process entries before/after: 7/10. Full external commands are omitted to avoid publishing unrelated checkout paths. These regex-filtered snapshots are an incomplete inventory, not continuous monitoring of load or other wrappers. Process presence is informational; it did not gate the test.

Metrics input SHA256: `a184b1b29ff1ec58b143aaccd4f5c98fa93b501f41f8c9e754cf786e8ffaaf1c`. Profiles input SHA256: `e8ddcde8c40881664006c9ac7d50a22ffbf2e265179834c0e6456d30462bcf5f`. Every source/pin SHA was checked against the measured Git commit; the complete warm-profile starting inventory and each leaf source are bound to that same inventory. Warm-profile source-binding mismatches: 0. Complete warm-profile set validated: True.

Size counter pin: `70bb859295edc2abb9ad81f8f6e31ab2adf8ca07`; counter SHA256: `6690ea76cf6031fa082bf5b1f85f3606db19508df511d0bb8d934048fa583220`; measurement-script SHA256: `b6576b49f90c4c00e52d046953d188a23f50e11c3e1082e9bad9d5a4a40d08c7`.

**Documented warning-parser correction:** this build initially exited successfully but was falsely marked invalid because the parser expected single-quoted `sorry` while Lean emitted backticks. The original false-invalid metrics and setup remain preserved. Reclassification counted the four authorized warnings in the unchanged SHA-bound raw log; timing, commands, sources and dependency evidence were not changed or rerun. Original execution script SHA256: `b6576b49f90c4c00e52d046953d188a23f50e11c3e1082e9bad9d5a4a40d08c7`; corrected analysis script SHA256: `6392a3bf352831155a5e6e4878075615dafe416b806eba0b45738fe5505b7ae8`. The renderer independently verified the exact one-line source replacement and the original/corrected census.

## 2. Size snapshot

| Git-tree measure | This snapshot | Prior | Δ |
| --- | --- | --- | --- |
| .lean files in tree | 89 | — | — |
| comment-only files (excluded) | 0 | — | — |
| counted files | 89 | — | — |
| total lines (counted files) | 11760 | — | — |
| non-comment code lines | 8759 | — | — |
| non-module files | 89 | — | — |

The pinned counter reported **89 non-module files**. This project uses the legacy import-file convention. The skill's zero-non-module structural criterion is **not met**; a module-system migration is outside this performance cleanup. The report is not an unqualified claim that every skill criterion passed.

The committed tree has 84 mathematical/library modules including the three Comparator challenge/control modules, plus five explicitly run scripts/audits. The timed facade closure builds 83 owned modules: `QuantumChannelContinuity.SourceCorrespondence` is the one supplemental mathematical module outside that closure. It is profiled directly in both serial profile sets as a supplemental measurement, rather than silently included in cold-build totals. The final `check.sh` explicitly builds it and the root audit imports it. Thus tree file count, timed module count and final full-check scope differ deliberately. Comment-only exclusions follow the unmodified pinned counter. The first timed snapshot was taken **after** the dead-code sweep, so this pair does not measure the sweep's performance benefit.

## 3. Headline table

| Metric | This snapshot | Prior | Δ | Relative Δ |
| --- | --- | --- | --- | --- |
| Wall (s) | 1,586.74 | — | — | — |
| User CPU (s) | 1,033.04 | — | — | — |
| System CPU (s) | 1,024.18 | — | — | — |
| Measured user + system CPU (s) | 2,057.22 | — | — | — |
| GNU time %CPU | 129.00 | — | — | — |
| Peak RSS (reported KiB) | 2,615,936.00 | — | — | — |
| Peak RSS (GiB) | 2.49 | — | — | — |
| Lake total jobs, including cached dependencies | 3,604.00 | — | — | — |
| Compiled own modules | 83.00 | — | — | — |
| Summed Built elapsed durations (s; NOT CPU) | 7,832.00 | — | — | — |
| Logged implied parallelism (sum / wall) | 4.94 | — | — | — |
| Logged elapsed ms / non-comment line | 894.17 | — | — | — |

This snapshot is the first clean baseline; no trend claim is made.

CPU/cores work-floor heuristic: **257.15 s**. Longest weighted owned import chain: **1,533.00 s**, covering 83/83 logged modules with committed source paths. These are heuristic diagnostics, not a scheduler prediction or achievable wall-time guarantee.

Weighted chain, imports first: `QuantumChannelContinuity.Foundations` → `QuantumChannelContinuity.Channels` → `QuantumChannelContinuity.TensorChannels` → `QuantumChannelContinuity.TensorOrder` → `QuantumChannelContinuity.StabilizedSchatten` → `QuantumChannelContinuity.DivergenceSchatten` → `QuantumChannelContinuity.TensorWords` → `QuantumChannelContinuity.TensorRegrouping` → `QuantumChannelContinuity.TensorStates` → `QuantumChannelContinuity.ChannelProducts` → `QuantumChannelContinuity.TensorRelative` → `QuantumChannelContinuity.RegularizationIdentities` → `QuantumChannelContinuity.FiniteInfinite` → `QuantumChannelContinuity.ContinuityAssembly` → `QuantumChannelContinuity.Main` → `ChannelRenyiContinuity` → `All`.

## 4. Build health

| Check | Result |
| --- | --- |
| Measurement valid | True |
| Build exit | 0 |
| Errors | 0 |
| Warnings | 37 |
| Intentional sorry warnings | 4 |
| Dependency artifacts unchanged | True |
| Profile source inventory unchanged | True |
| Profile source bindings match measured commit | True |

The authorized warning census is exactly three missing bodies in `ComparatorChallenges/ChannelRenyiContinuity.lean` (reference specifications) and one in `ComparatorChallenges/MissingProof.lean` (negative control). These four warnings are not holes in the proof library. Any additional or missing warning invalidates the measurement guard.

Observed sorry census: `{"ComparatorChallenges/ChannelRenyiContinuity.lean": 3, "ComparatorChallenges/MissingProof.lean": 1}`.

| Warning kind | Count |
| --- | --- |
| Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice | 8 |
| This simp argument is unused: | 4 |
| declaration uses `sorry` | 4 |
| try 'simp' instead of 'simpa' | 2 |
| `mul_le_mul_right'` has been deprecated: Use `mul_le_mul_left` instead | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.fixed_dilation_hockey_filter_of_slack_attainment`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.amplifiedOutput_choiInput`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.hermitianTracePair_apply`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.hermitian_nonneg_iff_trace`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.hermitianTrace_apply`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.hermitian_smul_nonneg`: | 1 |
| automatically included section variable(s) unused in theorem `QuantumChannelContinuity.hermitianTrace_nonneg`: | 1 |

Committed resource-limit overrides: `{"maxHeartbeats=1000000": 34, "maxHeartbeats=1200000": 2, "maxHeartbeats=1500000": 3, "maxHeartbeats=300000": 1, "maxHeartbeats=400000": 1, "maxHeartbeats=500000": 1, "maxHeartbeats=800000": 7, "maxRecDepth=8192": 4, "synthInstance.maxHeartbeats=100000": 21}`. The renderer reports existing overrides; it does not increase limits. No repository file-size threshold is claimed. Largest source files: `QuantumChannelContinuity/Schatten.lean` (676 lines); `QuantumChannelContinuity/Minimax.lean` (603 lines); `QuantumChannelContinuity/StateOrderApprox.lean` (446 lines); `QuantumChannelContinuity/StateSupportLimits.lean` (403 lines); `QuantumChannelContinuity/Filter.lean` (304 lines).

## 5. Heavy tail

| Logged module tier | Count | Prior | Δ |
| --- | --- | --- | --- |
| ≥10 s | 83 | — | — |
| ≥20 s | 83 | — | — |
| ≥30 s | 83 | — | — |
| ≥40 s | 83 | — | — |

| Rank | Own module | Built elapsed (s) | Prior (s) | Δ (s) |
| --- | --- | --- | --- | --- |
| 1 | `QuantumChannelContinuity.SDPCone` | 236.00 | — | — |
| 2 | `QuantumChannelContinuity.Schatten` | 194.00 | — | — |
| 3 | `QuantumChannelContinuity.TensorChannels` | 161.00 | — | — |
| 4 | `QuantumChannelContinuity.FilterAlignment` | 160.00 | — | — |
| 5 | `QuantumChannelContinuity.SDPTrace` | 160.00 | — | — |
| 6 | `QuantumChannelContinuity.FilterTensor` | 146.00 | — | — |
| 7 | `QuantumChannelContinuity.SDPPartialTrace` | 146.00 | — | — |
| 8 | `QuantumChannelContinuity.SlackTester` | 139.00 | — | — |
| 9 | `QuantumChannelContinuity.PowerRegrouping` | 134.00 | — | — |
| 10 | `QuantumChannelContinuity.TensorDilation` | 133.00 | — | — |
| 11 | `QuantumChannelContinuity.Filter` | 132.00 | — | — |
| 12 | `QuantumChannelContinuity.FoundationsMeasurement` | 128.00 | — | — |
| 13 | `QuantumChannelContinuity.SlackAttainment` | 128.00 | — | — |
| 14 | `QuantumChannelContinuity.ChannelProducts` | 125.00 | — | — |
| 15 | `QuantumChannelContinuity.ChannelDominationBounds` | 125.00 | — | — |
| 16 | `QuantumChannelContinuity.FoundationsDiagonal` | 124.00 | — | — |
| 17 | `QuantumChannelContinuity.TensorNaturality` | 120.00 | — | — |
| 18 | `QuantumChannelContinuity.StateOrder` | 120.00 | — | — |
| 19 | `QuantumChannelContinuity.TensorStates` | 112.00 | — | — |
| 20 | `QuantumChannelContinuity.Channels` | 111.00 | — | — |
| 21 | `QuantumChannelContinuity.FilterSlack` | 109.00 | — | — |
| 22 | `QuantumChannelContinuity.StateLimits` | 108.00 | — | — |
| 23 | `QuantumChannelContinuity.DivergenceSchatten` | 108.00 | — | — |
| 24 | `QuantumChannelContinuity.TensorOrder` | 107.00 | — | — |
| 25 | `QuantumChannelContinuity.StateSupportLimits` | 107.00 | — | — |
| 26 | `QuantumChannelContinuity.StateOrderApprox` | 107.00 | — | — |
| 27 | `QuantumChannelContinuity.TensorPowers` | 107.00 | — | — |
| 28 | `QuantumChannelContinuity.StabilizedSchatten` | 106.00 | — | — |
| 29 | `QuantumChannelContinuity.ThreePieceExponential` | 106.00 | — | — |
| 30 | `QuantumChannelContinuity.HockeyStick` | 104.00 | — | — |

Timing-visible extraction: 83 logged Built entries; reported compiled-own count 83. The current parser defines that count from the same entries, so equality is not an independent completeness audit. Millisecond and second entries are included. Cached Lake jobs have no own compile duration and are excluded; no independent count of omitted/unlogged compilation jobs is available.

## 6. Per-namespace elapsed-duration aggregation

| Namespace / facade | Summed elapsed (s) | Prior (s) | Δ (s) |
| --- | --- | --- | --- |
| All | 63.00 | — | — |
| ChannelContinuity | 726.00 | — | — |
| ChannelRenyiContinuity | 46.00 | — | — |
| ComparatorChallenges | 213.00 | — | — |
| QuantumChannelContinuity | 6,784.00 | — | — |

These are sums of logged module elapsed durations by first namespace component, **not per-namespace CPU measurements**. Each duration includes startup, import loading and build outputs under the observed load.

## 7. Serial warm own-file profiles

Campaign profile set: **nine specified paired files**, including supplemental `SourceCorrespondence`. Complete set: True. Expected files: `QuantumChannelContinuity/SDPCone.lean`, `QuantumChannelContinuity/Schatten.lean`, `QuantumChannelContinuity/TensorChannels.lean`, `QuantumChannelContinuity/FilterAlignment.lean`, `QuantumChannelContinuity/SDPTrace.lean`, `QuantumChannelContinuity/SourceCorrespondence.lean`, `QuantumChannelContinuity/Filter.lean`, `QuantumChannelContinuity/OrderConvexity.lean`, `QuantumChannelContinuity/RegularizationSup.lean`.

Actual current top-five own modules from the cold-build log: ['QuantumChannelContinuity.SDPCone', 'QuantumChannelContinuity.Schatten', 'QuantumChannelContinuity.TensorChannels', 'QuantumChannelContinuity.FilterAlignment', 'QuantumChannelContinuity.SDPTrace']. Warm-profile coverage complete: **True**. Missing files: []; unmapped modules: []. Current top-five files outside the frozen nine require a separate serial supplemental label; they must not be appended to the paired profile set.

| File | Warm wall (s) | Import | Typeclass | Simp | Elaboration | Type checking | Tactic execution |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `QuantumChannelContinuity/SDPCone.lean` | 112.79 | 58.00 | 47.20 | 3.56 | 0.37 | 0.92 | 1.69 |
| `QuantumChannelContinuity/Schatten.lean` | 65.56 | 40.10 | 55.70 | 3.28 | 2.08 | 2.37 | 10.20 |
| `QuantumChannelContinuity/TensorChannels.lean` | 48.48 | 23.10 | 14.50 | 3.95 | 0.66 | 1.84 | 1.51 |
| `QuantumChannelContinuity/FilterAlignment.lean` | 69.29 | 53.30 | 9.67 | 1.38 | 0.78 | 1.29 | 2.61 |
| `QuantumChannelContinuity/SDPTrace.lean` | 95.18 | 52.50 | 40.20 | 2.53 | 0.61 | 1.86 | 8.97 |
| `QuantumChannelContinuity/SourceCorrespondence.lean` | 39.58 | 31.90 | 1.23 | 0.13 | 0.11 | 0.14 | 0.73 |
| `QuantumChannelContinuity/Filter.lean` | 49.08 | 36.00 | 19.50 | 1.63 | 0.82 | 1.31 | 4.53 |
| `QuantumChannelContinuity/OrderConvexity.lean` | 36.67 | 28.70 | 0.29 | 0.01 | 0.02 | 0.06 | 0.09 |
| `QuantumChannelContinuity/RegularizationSup.lean` | 116.86 | 103.00 | 1.06 | 0.21 | 0.13 | 0.04 | 0.39 |

Phase values are seconds from the flat `--profile` cumulative counters. The pinned Lean `Lean.Util.Profile` documentation calls these **exclusive component execution times**: exclusion applies within an instrumented execution stack. Counters aggregate Lean threads/tasks, whose durations can overlap in wall time, so categories do not partition the GNU wall clock and their wall-time percentages need not total 100%. Their sum is not GNU process CPU or wall time; uninstrumented runtime and rounding can also differ. Structured `trace.profiler` trees are a separate profiler with nested durations that may overlap as well. A dash means that a flat label was absent, not a measured zero. Build elapsed durations and warm serial wall times measure different scopes. `SourceCorrespondence`, when present, is an explicitly additional paired supplemental profile; it is not one of the 83 cold-build modules.

Primary implementation references: [thread-local parent stack, exclusive subtraction and global category accumulation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/library/time_task.cpp), [steady-clock elapsed timer](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/util/timeit.h), and [flat-profiler option documentation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/Lean/Util/Profile.lean). Routing selects the largest qualified counter and lists other qualified counters. The >25%-of-warm-wall screen is a heuristic applied to aggregated timers, not a measured share of a wall-time partition.

**`QuantumChannelContinuity/SDPCone.lean`**: Largest qualified counter: `import` (58.00 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (47.20 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `ab2cca84a5d65809d5cffd93eac986dcb3ddab7e357b37295725d22ded440413`; raw profile SHA256: `5d89453c037aaa3c537a5e9114f3fc2126a1f3f9bd3658d0d2f054e470bdbec9`.

All reported cumulative phases: `{"attribute application": 6.93e-05, "congr simp thm": 0.0038, "elaboration": 0.372, "fix level params": 0.00618, "import": 58.0, "initialization": 0.062, "instantiate metavars": 0.0663, "interpretation": 3.71, "let-to-have transformation": 0.00136, "linting": 0.0596, "norm_num": 0.00275, "parsing": 0.014, "process pre-definitions": 0.0589, "ring": 0.0261, "share common exprs": 0.0228, "simp": 3.56, "tactic execution": 1.69, "type checking": 0.922, "typeclass inference": 47.2}`.

Reported event lines strictly over 100ms: 87 (87 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 58s
typeclass inference of Module took 643ms
typeclass inference of Module took 564ms
typeclass inference of Module took 1.02s
typeclass inference of Module took 886ms
typeclass inference of AddHomClass took 207ms
simp took 198ms
typeclass inference of ZeroHomClass took 591ms
typeclass inference of AddMonoidWithOne took 321ms
typeclass inference of HSMul took 557ms
typeclass inference of SMul took 422ms
typeclass inference of MulActionHomClass took 315ms
typeclass inference of Semiring took 179ms
typeclass inference of AddCommMonoid took 218ms
typeclass inference of SeminormedAddCommGroup took 183ms
typeclass inference of SMul took 1.7s
typeclass inference of Semiring took 148ms
typeclass inference of AddCommMonoid took 182ms
typeclass inference of SMul took 1.24s
typeclass inference of MulAction took 1.07s
typeclass inference of MulAction took 1.08s
simp took 109ms
typeclass inference of AddCommMonoid took 186ms
typeclass inference of MulAction took 1.22s
typeclass inference of NonUnitalSemiring took 231ms
typeclass inference of SMulWithZero took 1.01s
typeclass inference of NonUnitalSemiring took 262ms
typeclass inference of SMulWithZero took 1.06s
typeclass inference of PosSMulMono took 140ms
typeclass inference of MulAction took 1.91s
elaboration took 172ms
type checking took 161ms
type checking took 109ms
type checking took 153ms
typeclass inference of Module took 417ms
typeclass inference of Module took 287ms
typeclass inference of Module took 446ms
typeclass inference of SeminormedAddCommGroup took 103ms
typeclass inference of Module took 1.2s
typeclass inference of NormedSpace took 485ms
typeclass inference of ContinuousSMul took 244ms
tactic execution of Lean.Parser.Tactic.obtain took 111ms
typeclass inference of CoeFun took 105ms
typeclass inference of ProperSpace took 579ms
tactic execution of Lean.Parser.Tactic.obtain took 114ms
typeclass inference of Module took 292ms
typeclass inference of Module took 628ms
typeclass inference of NormedSpace took 255ms
typeclass inference of ContinuousSMul took 135ms
typeclass inference of Module took 473ms
typeclass inference of Module took 109ms
typeclass inference of SeminormedAddCommGroup took 125ms
typeclass inference of Module took 1.3s
typeclass inference of NormedSpace took 456ms
typeclass inference of ContinuousSMul took 223ms
type checking took 166ms
typeclass inference of Module took 431ms
typeclass inference of Module took 333ms
typeclass inference of Module took 1.05s
typeclass inference of Module took 1.02s
typeclass inference of Module took 774ms
typeclass inference of Module took 626ms
typeclass inference of NormedSpace took 256ms
typeclass inference of Module took 1.09s
typeclass inference of NormedSpace took 520ms
typeclass inference of ContinuousSMul took 411ms
typeclass inference of NormedSpace took 937ms
typeclass inference of LocallyConvexSpace took 139ms
tactic execution of Lean.Parser.Tactic.obtain took 216ms
typeclass inference of Module took 289ms
typeclass inference of Module took 297ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 138ms
typeclass inference of AddHomClass took 106ms
typeclass inference of ZeroHomClass took 215ms
typeclass inference of AddMonoidHomClass took 201ms
typeclass inference of AddMonoidHomClass took 181ms
typeclass inference of ZeroHomClass took 180ms
typeclass inference of ZeroHomClass took 196ms
typeclass inference of Semiring took 137ms
typeclass inference of AddMonoidWithOne took 131ms
typeclass inference of ZeroHomClass took 161ms
simp took 1.69s
simp took 1.17s
typeclass inference of AddMonoidHomClass took 165ms
typeclass inference of Ring took 109ms
typeclass inference of Ring took 108ms
type checking took 176ms
```

**`QuantumChannelContinuity/Schatten.lean`**: Largest qualified counter: `typeclass inference` (55.70 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. Other qualified counters: `import` (40.10 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `15b6bfdfbfea1da59b25aeb2915780a6955a1907175231ab0611d379cce48675`; raw profile SHA256: `e9f71b0b963e1fe353cd6189f4e907ac2560d3f576d06d8aa54518081cb16704`.

All reported cumulative phases: `{"aesop": 0.28, "attribute application": 0.000883, "compilation (IR)": 0.000805, "compilation (LCNF base)": 0.00391, "compilation (LCNF impure)": 0.00158, "compilation (LCNF mono)": 0.0057, "congr simp thm": 0.0525, "dsimp": 0.0444, "elaboration": 2.08, "fix level params": 0.0233, "import": 40.1, "initialization": 0.0365, "instantiate metavars": 0.0825, "interpretation": 5.51, "let-to-have transformation": 0.0047, "linting": 0.139, "norm_num": 0.0674, "parsing": 0.0845, "process pre-definitions": 0.134, "ring": 0.268, "share common exprs": 0.0995, "simp": 3.28, "tactic execution": 10.2, "type checking": 2.37, "typeclass inference": 55.7}`.

Reported event lines strictly over 100ms: 191 (193 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 40.1s
type checking took 107ms
simp took 101ms
typeclass inference of AddMonoidHomClass took 150ms
simp took 365ms
typeclass inference of Algebra took 153ms
typeclass inference of Algebra took 209ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 107ms
typeclass inference of CoeFun took 118ms
typeclass inference of CoeFun took 170ms
typeclass inference of Module took 128ms
typeclass inference of Algebra took 353ms
typeclass inference of Algebra took 226ms
typeclass inference of MulAction took 103ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 273ms
simp took 196ms
typeclass inference of Algebra took 106ms
typeclass inference of ContinuousFunctionalCalculus took 105ms
tactic execution of Lean.Parser.Tactic.refine took 104ms
type checking took 113ms
typeclass inference of Algebra took 108ms
typeclass inference of Algebra took 179ms
typeclass inference of ContinuousFunctionalCalculus took 145ms
simp took 224ms
typeclass inference of Module took 122ms
typeclass inference of Algebra took 231ms
typeclass inference of Algebra took 384ms
typeclass inference of HPow took 487ms
typeclass inference of Algebra took 227ms
typeclass inference of Algebra took 169ms
typeclass inference of ContinuousFunctionalCalculus took 202ms
typeclass inference of NonnegSpectrumClass took 139ms
typeclass inference of IsTopologicalRing took 161ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 244ms
typeclass inference of Algebra took 117ms
typeclass inference of ContinuousFunctionalCalculus took 138ms
typeclass inference of Algebra took 180ms
typeclass inference of Module took 124ms
typeclass inference of Module took 137ms
typeclass inference of Algebra took 210ms
typeclass inference of Algebra took 143ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 157ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 729ms
type checking took 194ms
typeclass inference of Algebra took 136ms
typeclass inference of Algebra took 170ms
typeclass inference of ContinuousFunctionalCalculus took 132ms
typeclass inference of Algebra took 138ms
typeclass inference of ContinuousFunctionalCalculus took 141ms
tactic execution of Lean.Parser.Tactic.refine took 121ms
typeclass inference of Algebra took 220ms
typeclass inference of ContinuousFunctionalCalculus took 102ms
simp took 234ms
typeclass inference of Algebra took 163ms
typeclass inference of ContinuousFunctionalCalculus took 159ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 202ms
interpretation of Mathlib.Tactic.FieldSimp._aux_Mathlib_Tactic_FieldSimp___elabRules_Mathlib_Tactic_FieldSimp_fieldSimp_1._boxed took 126ms
typeclass inference of Algebra took 156ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 115ms
type checking took 157ms
typeclass inference of Algebra took 172ms
typeclass inference of ContinuousFunctionalCalculus took 146ms
typeclass inference of Algebra took 284ms
typeclass inference of ContinuousFunctionalCalculus took 118ms
simp took 196ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 277ms
type checking took 129ms
typeclass inference of Algebra took 120ms
typeclass inference of Algebra took 106ms
typeclass inference of FaithfulSMul took 155ms
typeclass inference of Algebra took 185ms
typeclass inference of ContinuousFunctionalCalculus took 243ms
elaboration took 181ms
typeclass inference of Algebra took 105ms
typeclass inference of ContinuousFunctionalCalculus took 122ms
typeclass inference of NonnegSpectrumClass took 146ms
typeclass inference of IsTopologicalRing took 110ms
simp took 121ms
typeclass inference of Algebra took 313ms
typeclass inference of ContinuousFunctionalCalculus took 130ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 156ms
typeclass inference of ContinuousFunctionalCalculus took 103ms
type checking took 106ms
typeclass inference of HSMul took 156ms
typeclass inference of Algebra took 299ms
typeclass inference of ContinuousFunctionalCalculus took 174ms
elaboration took 103ms
typeclass inference of Module took 126ms
typeclass inference of Module took 105ms
typeclass inference of SMulZeroClass took 228ms
typeclass inference of SMulZeroClass took 117ms
typeclass inference of Module took 167ms
typeclass inference of Algebra took 254ms
typeclass inference of Algebra took 284ms
typeclass inference of PosSMulMono took 454ms
typeclass inference of Algebra took 203ms
typeclass inference of ContinuousFunctionalCalculus took 123ms
typeclass inference of Algebra took 138ms
typeclass inference of ContinuousFunctionalCalculus took 152ms
typeclass inference of IsTopologicalRing took 103ms
tactic execution of Lean.Parser.Tactic.simp took 133ms
typeclass inference of Algebra took 196ms
typeclass inference of ContinuousFunctionalCalculus took 104ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 121ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 107ms
type checking took 164ms
typeclass inference of Algebra took 219ms
typeclass inference of ContinuousFunctionalCalculus took 103ms
typeclass inference of Algebra took 121ms
typeclass inference of NonnegSpectrumClass took 102ms
typeclass inference of Algebra took 156ms
typeclass inference of ContinuousFunctionalCalculus took 108ms
simp took 102ms
aesop took 280ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 188ms
typeclass inference of Algebra took 142ms
type checking took 112ms
typeclass inference of HSMul took 157ms
typeclass inference of Algebra took 114ms
typeclass inference of ContinuousFunctionalCalculus took 109ms
elaboration took 135ms
typeclass inference of Algebra took 111ms
typeclass inference of ContinuousFunctionalCalculus took 122ms
typeclass inference of HSMul took 148ms
tactic execution of Lean.Parser.Tactic.refine took 136ms
typeclass inference of Algebra took 278ms
typeclass inference of LinearMap.CompatibleSMul took 130ms
type checking took 135ms
typeclass inference of HSMul took 172ms
typeclass inference of Algebra took 126ms
typeclass inference of ContinuousFunctionalCalculus took 163ms
typeclass inference of IsOrderedRing took 160ms
typeclass inference of Algebra took 128ms
typeclass inference of ContinuousFunctionalCalculus took 157ms
typeclass inference of Algebra took 172ms
typeclass inference of ContinuousFunctionalCalculus took 130ms
typeclass inference of ContinuousFunctionalCalculus took 106ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 130ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 112ms
interpretation of Lean.Elab.Tactic._aux_Mathlib_Tactic_Widget_Calc___elabRules_Lean_calcTactic_1._boxed took 256ms
typeclass inference of HSMul took 119ms
typeclass inference of Algebra took 230ms
typeclass inference of Algebra took 141ms
typeclass inference of Algebra took 171ms
typeclass inference of Algebra took 154ms
typeclass inference of ContinuousFunctionalCalculus took 112ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 319ms
typeclass inference of Algebra took 111ms
typeclass inference of ContinuousFunctionalCalculus took 107ms
tactic execution of Lean.Parser.Tactic.change took 109ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 243ms
typeclass inference of Algebra took 120ms
interpretation of Lean.Elab.Tactic._aux_Mathlib_Tactic_Widget_Calc___elabRules_Lean_calcTactic_1._boxed took 167ms
type checking took 183ms
typeclass inference of HSMul took 127ms
typeclass inference of HSMul took 151ms
typeclass inference of Nonempty took 101ms
simp took 190ms
typeclass inference of CoeFun took 118ms
typeclass inference of CoeFun took 112ms
typeclass inference of CoeFun took 159ms
typeclass inference of CoeFun took 131ms
typeclass inference of CoeFun took 103ms
simp took 323ms
elaboration took 126ms
typeclass inference of AddMonoidHomClass took 238ms
typeclass inference of HSMul took 134ms
typeclass inference of CoeFun took 119ms
elaboration took 147ms
tactic execution of Lean.Parser.Tactic.simpa took 151ms
typeclass inference of CoeFun took 103ms
typeclass inference of CoeFun took 108ms
typeclass inference of HSMul took 111ms
typeclass inference of CoeFun took 178ms
typeclass inference of CoeFun took 128ms
typeclass inference of CoeFun took 143ms
typeclass inference of CoeFun took 135ms
typeclass inference of CoeFun took 115ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 440ms
typeclass inference of CoeFun took 129ms
typeclass inference of CoeFun took 183ms
typeclass inference of AddMonoidHomClass took 245ms
typeclass inference of CoeFun took 116ms
tactic execution of Lean.Parser.Tactic.change took 171ms
typeclass inference of HSMul took 169ms
elaboration took 154ms
typeclass inference of ZeroHomClass took 127ms
tactic execution of Lean.Parser.Tactic.simpa took 141ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 157ms
tactic execution of Lean.Parser.Tactic.refine took 265ms
type checking took 131ms
```

**`QuantumChannelContinuity/TensorChannels.lean`**: Largest qualified counter: `import` (23.10 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (14.50 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `e561e8318f2f13c9c3a7773c21ed84e5bfda4adc6bed966aacd38903c40edfa6`; raw profile SHA256: `9f3ae678a3492d68bad434d7cd89c8c7670b6e02be03f68c727e6564458d9c7c`.

All reported cumulative phases: `{"attribute application": 7.539999999999999e-05, "blocked (unaccounted)": 0.000495, "congr simp thm": 0.018, "elaboration": 0.656, "fix level params": 0.00642, "import": 23.1, "initialization": 0.0407, "instantiate metavars": 0.146, "interpretation": 2.23, "let-to-have transformation": 0.000493, "linting": 0.0985, "parsing": 0.0062900000000000005, "process pre-definitions": 0.0535, "share common exprs": 0.0286, "simp": 3.95, "tactic execution": 1.51, "type checking": 1.84, "typeclass inference": 14.5}`.

Reported event lines strictly over 100ms: 41 (42 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 23.1s
typeclass inference of ZeroHomClass took 288ms
typeclass inference of Nonempty took 153ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 183ms
simp took 146ms
simp took 675ms
simp took 393ms
simp took 404ms
typeclass inference of Nonempty took 166ms
typeclass inference of Nonempty took 132ms
typeclass inference of Nonempty took 105ms
typeclass inference of Nonempty took 136ms
typeclass inference of Nonempty took 169ms
typeclass inference of Nonempty took 108ms
typeclass inference of Nonempty took 165ms
typeclass inference of Nonempty took 120ms
typeclass inference of Nonempty took 174ms
typeclass inference of Nonempty took 119ms
simp took 1.47s
typeclass inference of Nonempty took 134ms
typeclass inference of Nonempty took 105ms
typeclass inference of Nonempty took 123ms
typeclass inference of Nonempty took 125ms
typeclass inference of Nonempty took 112ms
typeclass inference of AddHomClass took 317ms
typeclass inference of Nonempty took 117ms
typeclass inference of Nonempty took 103ms
typeclass inference of Nonempty took 102ms
typeclass inference of Nonempty took 145ms
simp took 196ms
instantiate metavars took 137ms
type checking took 639ms
typeclass inference of ZeroHomClass took 302ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 220ms
typeclass inference of AddHomClass took 147ms
type checking took 282ms
tactic execution of Lean.Parser.Tactic.obtain took 300ms
elaboration took 416ms
type checking took 134ms
type checking took 138ms
type checking took 245ms
```

**`QuantumChannelContinuity/FilterAlignment.lean`**: Largest qualified counter: `import` (53.30 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `eab78d995aec86038f213000a12ebef7bf58effa8a86e757acd27c2a5db787c4`; raw profile SHA256: `8fb0c1341797a110e002b2bfa0ffbbe45e5f9818813472e2f0700bd87d1e778e`.

All reported cumulative phases: `{"attribute application": 0.00429, "congr simp thm": 0.018, "dsimp": 0.00173, "elaboration": 0.776, "fix level params": 0.0152, "import": 53.3, "initialization": 0.051, "instantiate metavars": 0.0416, "interpretation": 5.33, "let-to-have transformation": 0.00232, "linting": 0.0522, "norm_num": 0.009880000000000002, "parsing": 0.0222, "process pre-definitions": 0.0549, "ring": 0.11, "share common exprs": 0.066, "simp": 1.38, "tactic execution": 2.61, "type checking": 1.29, "typeclass inference": 9.67}`.

Reported event lines strictly over 100ms: 33 (33 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 53.3s
tactic execution of Lean.Parser.Tactic.rewriteSeq took 110ms
simp took 129ms
typeclass inference of Add took 183ms
typeclass inference of AddHomClass took 114ms
simp took 260ms
type checking took 156ms
typeclass inference of CoeFun took 107ms
typeclass inference of ZeroHomClass took 177ms
typeclass inference of ZeroHomClass took 108ms
typeclass inference of SeminormedAddCommGroup took 372ms
typeclass inference of ZeroHomClass took 430ms
type checking took 157ms
typeclass inference of ZeroHomClass took 129ms
typeclass inference of Nonempty took 253ms
typeclass inference of ZeroHomClass took 104ms
typeclass inference of CoeFun took 138ms
type checking took 106ms
tactic execution of Lean.Parser.Tactic.simpa took 129ms
simp took 137ms
typeclass inference of CoeFun took 110ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 925ms
tactic execution of Lean.Parser.Tactic.obtain took 140ms
typeclass inference of CoeFun took 124ms
tactic execution of Lean.Parser.Tactic.obtain took 116ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 113ms
tactic execution of Lean.Parser.Tactic.change took 179ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 128ms
simp took 220ms
tactic execution of Lean.Parser.Tactic.obtain took 155ms
tactic execution of Lean.Parser.Tactic.exact took 587ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 1.71s
type checking took 191ms
```

**`QuantumChannelContinuity/SDPTrace.lean`**: Largest qualified counter: `import` (52.50 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (40.20 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `42376ffe8705eb9591d75e599c87060502b2763c824dcb6c84020346579e48bb`; raw profile SHA256: `2c472322bf5a12e074f2b2399d7cd0b810744b0bec5a565fa49f5ec03d5016ef`.

All reported cumulative phases: `{"attribute application": 0.0165, "congr simp thm": 0.009949999999999999, "elaboration": 0.609, "fix level params": 0.0061600000000000005, "import": 52.5, "initialization": 0.0562, "instantiate metavars": 0.00638, "interpretation": 3.26, "let-to-have transformation": 0.0125, "linting": 0.0824, "parsing": 0.0305, "process pre-definitions": 0.115, "share common exprs": 0.024, "simp": 2.53, "tactic execution": 8.97, "type checking": 1.86, "typeclass inference": 40.2}`.

Reported event lines strictly over 100ms: 56 (56 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 52.5s
typeclass inference of Module took 293ms
typeclass inference of StarModule took 187ms
typeclass inference of Module took 442ms
typeclass inference of FiniteDimensional took 162ms
type checking took 111ms
typeclass inference of Module took 510ms
typeclass inference of Module took 386ms
typeclass inference of Module took 403ms
typeclass inference of Module took 128ms
simp took 583ms
typeclass inference of Module took 392ms
typeclass inference of Module took 300ms
typeclass inference of Algebra took 152ms
simp took 585ms
elaboration took 111ms
type checking took 103ms
type checking took 130ms
typeclass inference of CoeFun took 111ms
typeclass inference of Module took 563ms
typeclass inference of CoeFun took 133ms
type checking took 124ms
typeclass inference of AddCommGroup took 501ms
typeclass inference of AddCommGroup took 119ms
typeclass inference of AddCommGroup took 116ms
typeclass inference of AddCommGroup took 108ms
typeclass inference of Module took 529ms
typeclass inference of FiniteDimensional took 214ms
tactic execution of Lean.Parser.Tactic.apply took 8.08s
typeclass inference of Module took 370ms
type checking took 122ms
type checking took 196ms
typeclass inference of Module took 580ms
typeclass inference of Module took 702ms
typeclass inference of Module took 171ms
typeclass inference of Module took 527ms
typeclass inference of Module took 230ms
simp took 1.01s
typeclass inference of CoeFun took 134ms
typeclass inference of HSMul took 751ms
typeclass inference of HSMul took 174ms
typeclass inference of Module took 118ms
typeclass inference of HSMul took 788ms
typeclass inference of AddCommSemigroup took 144ms
typeclass inference of AddRightMono took 139ms
typeclass inference of Semiring took 330ms
typeclass inference of AddCommMonoid took 404ms
typeclass inference of SeminormedAddCommGroup took 169ms
typeclass inference of DistribSMul took 2.49s
typeclass inference of DistribSMul took 1.18s
type checking took 133ms
typeclass inference of CoeFun took 108ms
typeclass inference of AddCommSemigroup took 141ms
typeclass inference of AddRightMono took 156ms
typeclass inference of AddMonoidHomClass took 647ms
typeclass inference of CoeFun took 107ms
```

**`QuantumChannelContinuity/SourceCorrespondence.lean`**: Largest qualified counter: `import` (31.90 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `1319b701c9fc33fd4ab8b36720b0bbf7909a7e4f61888c29752b8b93810ee2ef`; raw profile SHA256: `d6aba90752ae2d6f4292ca8a4dedcf9587b6cdc53b0333c5ab2553c54d81ac28`.

All reported cumulative phases: `{"attribute application": 6.07e-05, "congr simp thm": 0.00392, "elaboration": 0.114, "fix level params": 0.00075, "import": 31.9, "initialization": 0.07909999999999999, "instantiate metavars": 0.00458, "interpretation": 1.46, "let-to-have transformation": 0.000324, "linting": 0.00561, "parsing": 0.00471, "process pre-definitions": 0.00661, "share common exprs": 0.00567, "simp": 0.129, "tactic execution": 0.726, "type checking": 0.142, "typeclass inference": 1.23}`.

Reported event lines strictly over 100ms: 5 (5 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 31.9s
tactic execution of Lean.Parser.Tactic.change took 112ms
typeclass inference of ZeroHomClass took 188ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 183ms
tactic execution of Lean.Parser.Tactic.exact took 162ms
```

**`QuantumChannelContinuity/Filter.lean`**: Largest qualified counter: `import` (36.00 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (19.50 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `fb391a13524509379adc5bc8aa80bf846155f2d76cdbaaf028ec6d857f742da2`; raw profile SHA256: `1c60358bb77edc7e3c4b12ccfb24078cfded8e37a36a2153b1c8dd2c58951f91`.

All reported cumulative phases: `{"attribute application": 0.00027400000000000005, "congr simp thm": 0.0127, "elaboration": 0.82, "fix level params": 0.0182, "import": 36.0, "initialization": 0.043, "instantiate metavars": 0.039, "interpretation": 4.15, "let-to-have transformation": 0.00292, "linting": 0.0569, "norm_num": 0.0176, "parsing": 0.0254, "process pre-definitions": 0.0487, "ring": 0.0992, "share common exprs": 0.056799999999999996, "simp": 1.63, "tactic execution": 4.53, "type checking": 1.31, "typeclass inference": 19.5}`.

Reported event lines strictly over 100ms: 45 (45 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 36s
typeclass inference of CoeT took 187ms
typeclass inference of AddMonoidHomClass took 113ms
simp took 143ms
simp took 179ms
simp took 299ms
tactic execution of Lean.Parser.Tactic.simpa took 435ms
type checking took 220ms
tactic execution of Lean.Parser.Tactic.change took 117ms
tactic execution of Lean.Parser.Tactic.refine took 140ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 266ms
typeclass inference of CoeFun took 116ms
typeclass inference of CoeFun took 112ms
tactic execution of Lean.Parser.Tactic.exact took 130ms
typeclass inference of CoeFun took 143ms
typeclass inference of CoeFun took 119ms
tactic execution of Lean.Parser.Tactic.exact took 200ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 151ms
tactic execution of Lean.Parser.Tactic.obtain took 108ms
typeclass inference of ZeroHomClass took 415ms
tactic execution of Lean.Parser.Tactic.simpa took 232ms
typeclass inference of AddHomClass took 279ms
type checking took 419ms
tactic execution of Lean.Parser.Tactic.change took 144ms
typeclass inference of Submodule.HasOrthogonalProjection took 115ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 199ms
typeclass inference of CoeFun took 107ms
typeclass inference of CoeFun took 103ms
typeclass inference of CoeFun took 133ms
typeclass inference of Module took 198ms
typeclass inference of Module took 130ms
typeclass inference of Algebra took 281ms
typeclass inference of Algebra took 141ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 102ms
typeclass inference of Module took 134ms
typeclass inference of Algebra took 107ms
typeclass inference of CoeFun took 175ms
tactic execution of Lean.Parser.Tactic.obtain took 142ms
simp took 222ms
typeclass inference of CoeFun took 122ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 138ms
tactic execution of Lean.Parser.Tactic.exact took 321ms
typeclass inference of CoeFun took 236ms
typeclass inference of CoeFun took 101ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 1.96s
```

**`QuantumChannelContinuity/OrderConvexity.lean`**: Largest qualified counter: `import` (28.70 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `fb94c303540e604639a0e0ac2c0f3c627c0d1ff072d91567be059828be197afb`; raw profile SHA256: `cef021f53b77602e25b0539b781d8d494eba88c5f7184bdfcb44a7f39ec6dfc4`.

All reported cumulative phases: `{"attribute application": 6.02e-05, "blocked (unaccounted)": 0.0010500000000000002, "congr simp thm": 0.00073, "elaboration": 0.0209, "fix level params": 0.00046300000000000003, "import": 28.7, "initialization": 0.037700000000000004, "instantiate metavars": 0.000517, "interpretation": 2.49, "let-to-have transformation": 8.05e-05, "linting": 0.0115, "norm_num": 0.288, "parsing": 0.0030600000000000002, "process pre-definitions": 0.0053, "ring": 0.0519, "share common exprs": 0.00704, "simp": 0.0106, "tactic execution": 0.0906, "type checking": 0.0621, "typeclass inference": 0.293}`.

Reported event lines strictly over 100ms: 2 (2 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 28.7s
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_linarith_1._boxed took 110ms
```

**`QuantumChannelContinuity/RegularizationSup.lean`**: Largest qualified counter: `import` (103.00 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `e5bba3db0c8dc9d2923a340f0dd7fce2b5c87c53fc925bfe07eae518f7d7c450`; raw profile SHA256: `ab7e5036fca2681aec05dbfb1916f91b2ec61a67fbe87143ad5fc5c8988c05eb`.

All reported cumulative phases: `{"attribute application": 7.049999999999999e-05, "compilation (IR)": 0.000584, "compilation (LCNF base)": 0.00478, "compilation (LCNF impure)": 0.000596, "compilation (LCNF mono)": 0.0029100000000000003, "congr simp thm": 0.00352, "elaboration": 0.133, "fix level params": 0.00023799999999999998, "import": 103.0, "initialization": 0.051, "instantiate metavars": 0.000519, "interpretation": 5.28, "let-to-have transformation": 0.000509, "linting": 0.044700000000000004, "parsing": 0.0193, "process pre-definitions": 0.0124, "share common exprs": 0.00242, "simp": 0.212, "tactic execution": 0.387, "type checking": 0.0373, "typeclass inference": 1.06}`.

Reported event lines strictly over 100ms: 2 (2 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 103s
tactic execution of Lean.Parser.Tactic.refine took 185ms
```

## 8. Findings ranked by actionability

No intervention record was supplied. These profiles establish measurements and candidates; they do not claim an applied or successful optimization.

The separately bound [explicit import-closure audit](docs/elaboration/import-closure.json) finds a smaller source import closure in each of the six retained leaves, while the timed default-target union remains **3,584 non-toolchain modules** before and after. Narrower leaf imports do not establish a smaller global union or a timing benefit by themselves; explicit Lean/Init/Std/Lake boundaries and implicit prelude edges are excluded as disclosed in that audit.

Keep an intervention only with measured evidence in its relevant phase (the cleanup skill uses ≥2 s or ≥10%), without moving cost to a worse consumer. Import-bound measurements route to consumer import narrowing. Large unassigned elaboration requires a per-declaration trace; diffuse typeclass time does not by itself identify a cacheable class.

## 9. What is not established

This snapshot does not prove global optimality, a statistically stable speedup, or equal background load. The logged sum is not CPU, and implied parallelism is a diagnostic ratio. GNU time 1.10 on this Darwin host reports RSS in KiB (validated against the platform's byte-valued resource counter); GiB is KiB / 1,048,576. Its peak RSS is the maximum accounted process/child RSS, not the sum of concurrent workers' simultaneous memory. Flat profiler categories are exclusive within instrumented execution stacks; aggregation across parallel threads/tasks can exceed wall time. They are not a wall-time partition, and their counter sum is not process CPU/wall time. Structured nested trace durations may also overlap. The import-chain estimate excludes upstream compilation because dependency oleans are inputs, and its elapsed weights can include contention.

Two snapshots cannot establish a monotonic regression across three reports. No Δlines × prior-ms/line calculation predicts measured CPU: the normalized metric uses elapsed-duration sums instead. Unprofiled modules and unattributed elaboration remain outside a causal claim. Other Lean processes alone do not establish artifact mutation or invalidity. The legacy module-header criterion remains unmet. Missing warm profiles make this a preliminary diagnostic; invalid inventories, unsuccessful profile exits or unpreserved artifacts are rejected before rendering.

## 10. Methodology and exact commands

The recorded timed command was:

```bash
/opt/homebrew/bin/gtime -v ./run-lake.sh --no-ansi --no-cache build All ChannelContinuity QuantumChannelContinuity ComparatorChallenges
```

Recorded warm commands, executed sequentially:

```bash
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/SDPCone.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/Schatten.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/TensorChannels.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/FilterAlignment.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/SDPTrace.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/SourceCorrespondence.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/Filter.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/OrderConvexity.lean
/opt/homebrew/bin/gtime -v ./run-lake.sh env lean --profile QuantumChannelContinuity/RegularizationSup.lean
```

Replay from the recorded commit using the dependency preparation, pinned skill checkout and GNU-time instructions in [the elaboration guide](docs/elaboration/README.md). Choose a fresh label; the measurement script rejects an existing build-label directory. Profile after the build, never in parallel batches.

## 11. Pointers

- [Elaboration test skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration-test/SKILL.md)
- [Measured cleanup skill](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-elaboration/SKILL.md)
- [Dead-code sweep, before this baseline](docs/DEAD_CODE_SWEEP_2026-10-06.md)
- [Reproduction guide](docs/elaboration/README.md)
- [Metrics evidence](docs/elaboration/before/metrics.json)
- [Warm profile evidence](docs/elaboration/before/profiles.json)
- [Original false-invalid metrics](docs/elaboration/before/metrics-original-parser.json)
- [Parser-only correction record](docs/elaboration/before/parser-correction.json)
- [Unchanged timed build log](docs/elaboration/before/build.txt)
- [Original execution setup](docs/elaboration/before/setup.json)
- [Exact original execution script](docs/elaboration/before/execution-measurement-script.py)
- [Exact corrected parser script](docs/elaboration/before/corrected-warning-parser-script.py)
