<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->

# Elaboration report — 2026-10-06 — AFTER

## 1. Setup and provenance

Measured commit: `8765c21753175381a57b29fa9469b35675515b2c`. UTC window: `2026-10-07T00:26:37.635181+00:00` to `2026-10-07T00:53:57.254527+00:00`. Host: `macOS-27.2-arm64-arm-64bit-Mach-O`; reported logical cores: 8. Lean: `Lean (version 4.29.0-rc6, arm64-apple-darwin24.6.0, commit 00659f8e6071d7e46131ed643bf8003b99b044e9, Release)`.

The report/filename date `2026-10-06` labels the cleanup campaign, not necessarily this run's UTC date. The recorded measurement UTC timestamps are authoritative.

Timing tool: `time (GNU Time) 1.10` using `-v`. Scheduling: Lake default; no explicit concurrency override. Explicit targets: `All, ChannelContinuity, QuantumChannelContinuity, ComparatorChallenges`. These targets cover the committed facade import closure plus Comparator specifications/controls. Lake's default library globs select root modules, not every submodule. The timed scope is 83 owned modules; the supplementary `SourceCorrespondence` module is outside that cold-build closure.

Only the checkout's resolved `.lake/build` was invalidated after rejecting symlinks or dependency caches nested in that subtree. Dependencies remained inputs. No `lake clean` or `lake update` is part of this measurement.

Observed Lean/Lake process entries before/after: 6/6. Full external commands are omitted to avoid publishing unrelated checkout paths. These regex-filtered snapshots are an incomplete inventory, not continuous monitoring of load or other wrappers. Process presence is informational; it did not gate the test.

Metrics input SHA256: `9b6866759285d10ed4900fbccb13860c970985b83fa926c903ccbc92a8eb3d3d`. Profiles input SHA256: `e752721095dca90fe629e72bd40dfd0c93301d7436a85d3f17f79ce4ad8cbde4`. Every source/pin SHA was checked against the measured Git commit; the complete warm-profile starting inventory and each leaf source are bound to that same inventory. Warm-profile source-binding mismatches: 0. Complete warm-profile set validated: True.

Size counter pin: `70bb859295edc2abb9ad81f8f6e31ab2adf8ca07`; counter SHA256: `6690ea76cf6031fa082bf5b1f85f3606db19508df511d0bb8d934048fa583220`; measurement-script SHA256: `6392a3bf352831155a5e6e4878075615dafe416b806eba0b45738fe5505b7ae8`.

## 2. Size snapshot

| Git-tree measure | This snapshot | Prior | Δ |
| --- | --- | --- | --- |
| .lean files in tree | 89 | 89 | +0 |
| comment-only files (excluded) | 0 | 0 | +0 |
| counted files | 89 | 89 | +0 |
| total lines (counted files) | 11772 | 11760 | +12 |
| non-comment code lines | 8770 | 8759 | +11 |
| non-module files | 89 | 89 | +0 |

The pinned counter reported **89 non-module files**. This project uses the legacy import-file convention. The skill's zero-non-module structural criterion is **not met**; a module-system migration is outside this performance cleanup. The report is not an unqualified claim that every skill criterion passed.

The committed tree has 84 mathematical/library modules including the three Comparator challenge/control modules, plus five explicitly run scripts/audits. The timed facade closure builds 83 owned modules: `QuantumChannelContinuity.SourceCorrespondence` is the one supplemental mathematical module outside that closure. It is profiled directly in both serial profile sets as a supplemental measurement, rather than silently included in cold-build totals. The final `check.sh` explicitly builds it and the root audit imports it. Thus tree file count, timed module count and final full-check scope differ deliberately. Comment-only exclusions follow the unmodified pinned counter. The first timed snapshot was taken **after** the dead-code sweep, so this pair does not measure the sweep's performance benefit.

## 3. Headline table

| Metric | This snapshot | Prior | Δ | Relative Δ |
| --- | --- | --- | --- | --- |
| Wall (s) | 1,616.34 | 1,586.74 | +29.60 | +1.9% |
| User CPU (s) | 1,076.03 | 1,033.04 | +42.99 | +4.2% |
| System CPU (s) | 895.05 | 1,024.18 | -129.13 | -12.6% |
| Measured user + system CPU (s) | 1,971.08 | 2,057.22 | -86.14 | -4.2% |
| GNU time %CPU | 121.00 | 129.00 | -8.00 | -6.2% |
| Peak RSS (reported KiB) | 3,116,208.00 | 2,615,936.00 | +500,272.00 | +19.1% |
| Peak RSS (GiB) | 2.97 | 2.49 | +0.48 | +19.1% |
| Lake total jobs, including cached dependencies | 3,604.00 | 3,604.00 | +0.00 | +0.0% |
| Compiled own modules | 83.00 | 83.00 | +0.00 | +0.0% |
| Summed Built elapsed durations (s; NOT CPU) | 6,706.00 | 7,832.00 | -1,126.00 | -14.4% |
| Logged implied parallelism (sum / wall) | 4.15 | 4.94 | -0.79 | -15.9% |
| Logged elapsed ms / non-comment line | 764.65 | 894.17 | -129.51 | -14.5% |

Execution script SHAs differ only by the independently checked one-line intentional-sorry warning parser correction. Original execution SHA/timing and false-invalid baseline result are preserved; the saved raw log was reclassified without retiming. This is a documented analysis correction, not silently identical instrumentation. Logged implied parallelism differs by more than the report's 10% descriptive tolerance; no wall-speedup claim. Contention indicators detected: same-file logged times moved both up and down by more than 10%. Co-running Lean/Lake commands were observed. Presence alone neither invalidates the run nor proves contamination; actual source/dependency mutation guards determine validity.

CPU/cores work-floor heuristic: **246.38 s**. Longest weighted owned import chain: **1,594.00 s**, covering 83/83 logged modules with committed source paths. These are heuristic diagnostics, not a scheduler prediction or achievable wall-time guarantee.

Weighted chain, imports first: `QuantumChannelContinuity.Foundations` → `QuantumChannelContinuity.FoundationsMeasurement` → `QuantumChannelContinuity.FoundationsDiagonal` → `QuantumChannelContinuity.FoundationsTesting` → `QuantumChannelContinuity.FoundationsWeakTesting` → `QuantumChannelContinuity.ChannelTesting` → `QuantumChannelContinuity.Regularization` → `QuantumChannelContinuity.TensorWords` → `QuantumChannelContinuity.TensorRegrouping` → `QuantumChannelContinuity.TensorStates` → `QuantumChannelContinuity.ChannelProducts` → `QuantumChannelContinuity.TensorRelative` → `QuantumChannelContinuity.RegularizationIdentities` → `QuantumChannelContinuity.FiniteInfinite` → `QuantumChannelContinuity.ContinuityAssembly` → `QuantumChannelContinuity.Main` → `ChannelRenyiContinuity` → `All`.

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

Committed resource-limit overrides: `{"maxHeartbeats=1000000": 34, "maxHeartbeats=1200000": 2, "maxHeartbeats=1500000": 3, "maxHeartbeats=300000": 1, "maxHeartbeats=400000": 1, "maxHeartbeats=500000": 1, "maxHeartbeats=800000": 7, "maxRecDepth=8192": 4, "synthInstance.maxHeartbeats=100000": 21}`. The renderer reports existing overrides; it does not increase limits. No repository file-size threshold is claimed. Largest source files: `QuantumChannelContinuity/Schatten.lean` (676 lines); `QuantumChannelContinuity/Minimax.lean` (603 lines); `QuantumChannelContinuity/StateOrderApprox.lean` (446 lines); `QuantumChannelContinuity/StateSupportLimits.lean` (403 lines); `QuantumChannelContinuity/Filter.lean` (305 lines).

## 5. Heavy tail

| Logged module tier | Count | Prior | Δ |
| --- | --- | --- | --- |
| ≥10 s | 83 | 83 | +0 |
| ≥20 s | 78 | 83 | -5 |
| ≥30 s | 76 | 83 | -7 |
| ≥40 s | 67 | 83 | -16 |

| Rank | Own module | Built elapsed (s) | Prior (s) | Δ (s) |
| --- | --- | --- | --- | --- |
| 1 | `QuantumChannelContinuity.ContinuityAssembly` | 222.00 | 70.00 | +152.00 |
| 2 | `QuantumChannelContinuity.StabilizedSchatten` | 177.00 | 106.00 | +71.00 |
| 3 | `QuantumChannelContinuity.ComplexTraceHolder` | 174.00 | 95.00 | +79.00 |
| 4 | `QuantumChannelContinuity.SDPCone` | 161.00 | 236.00 | -75.00 |
| 5 | `QuantumChannelContinuity.TracePowerBounds` | 153.00 | 86.00 | +67.00 |
| 6 | `QuantumChannelContinuity.TensorWords` | 151.00 | 87.00 | +64.00 |
| 7 | `QuantumChannelContinuity.RegularizationIdentities` | 150.00 | 73.00 | +77.00 |
| 8 | `QuantumChannelContinuity.SDPTrace` | 143.00 | 160.00 | -17.00 |
| 9 | `QuantumChannelContinuity.Schatten` | 130.00 | 194.00 | -64.00 |
| 10 | `QuantumChannelContinuity.StateSupportLimits` | 128.00 | 107.00 | +21.00 |
| 11 | `QuantumChannelContinuity.ConcreteMain` | 126.00 | 72.00 | +54.00 |
| 12 | `ComparatorChallenges.ChannelRenyiContinuity` | 123.00 | 71.00 | +52.00 |
| 13 | `ComparatorChallenges.WrongStatement` | 123.00 | 71.00 | +52.00 |
| 14 | `ComparatorChallenges.MissingProof` | 123.00 | 71.00 | +52.00 |
| 15 | `QuantumChannelContinuity.ChoiSupport` | 120.00 | 96.00 | +24.00 |
| 16 | `QuantumChannelContinuity.FoundationsTesting` | 119.00 | 73.00 | +46.00 |
| 17 | `QuantumChannelContinuity.TensorDilation` | 119.00 | 133.00 | -14.00 |
| 18 | `QuantumChannelContinuity.SlackTester` | 119.00 | 139.00 | -20.00 |
| 19 | `QuantumChannelContinuity.SDPPartialTrace` | 119.00 | 146.00 | -27.00 |
| 20 | `QuantumChannelContinuity.FilterAlignment` | 114.00 | 160.00 | -46.00 |
| 21 | `QuantumChannelContinuity.FilterHockey` | 114.00 | 78.00 | +36.00 |
| 22 | `QuantumChannelContinuity.DilationExistence` | 114.00 | 78.00 | +36.00 |
| 23 | `QuantumChannelContinuity.FilterTensor` | 113.00 | 146.00 | -33.00 |
| 24 | `QuantumChannelContinuity.TensorChannels` | 109.00 | 161.00 | -52.00 |
| 25 | `QuantumChannelContinuity.FiniteInfinite` | 97.00 | 71.00 | +26.00 |
| 26 | `QuantumChannelContinuity.RegularizationLimits` | 97.00 | 71.00 | +26.00 |
| 27 | `QuantumChannelContinuity.StateOrderDuality` | 96.00 | 89.00 | +7.00 |
| 28 | `QuantumChannelContinuity.DivergenceSchatten` | 94.00 | 108.00 | -14.00 |
| 29 | `QuantumChannelContinuity.FoundationsDiagonal` | 92.00 | 124.00 | -32.00 |
| 30 | `QuantumChannelContinuity.TensorNaturality` | 89.00 | 120.00 | -31.00 |

Timing-visible extraction: 83 logged Built entries; reported compiled-own count 83. The current parser defines that count from the same entries, so equality is not an independent completeness audit. Millisecond and second entries are included. Cached Lake jobs have no own compile duration and are excluded; no independent count of omitted/unlogged compilation jobs is available.

## 6. Per-namespace elapsed-duration aggregation

| Namespace / facade | Summed elapsed (s) | Prior (s) | Δ (s) |
| --- | --- | --- | --- |
| All | 37.00 | 63.00 | -26.00 |
| ChannelContinuity | 371.00 | 726.00 | -355.00 |
| ChannelRenyiContinuity | 50.00 | 46.00 | +4.00 |
| ComparatorChallenges | 369.00 | 213.00 | +156.00 |
| QuantumChannelContinuity | 5,879.00 | 6,784.00 | -905.00 |

These are sums of logged module elapsed durations by first namespace component, **not per-namespace CPU measurements**. Each duration includes startup, import loading and build outputs under the observed load.

## 7. Serial warm own-file profiles

Campaign profile set: **nine specified paired files**, including supplemental `SourceCorrespondence`. Complete set: True. Expected files: `QuantumChannelContinuity/SDPCone.lean`, `QuantumChannelContinuity/Schatten.lean`, `QuantumChannelContinuity/TensorChannels.lean`, `QuantumChannelContinuity/FilterAlignment.lean`, `QuantumChannelContinuity/SDPTrace.lean`, `QuantumChannelContinuity/SourceCorrespondence.lean`, `QuantumChannelContinuity/Filter.lean`, `QuantumChannelContinuity/OrderConvexity.lean`, `QuantumChannelContinuity/RegularizationSup.lean`.

Actual current top-five own modules from the cold-build log: ['QuantumChannelContinuity.ContinuityAssembly', 'QuantumChannelContinuity.StabilizedSchatten', 'QuantumChannelContinuity.ComplexTraceHolder', 'QuantumChannelContinuity.SDPCone', 'QuantumChannelContinuity.TracePowerBounds']. Warm-profile coverage complete: **True**. Missing files: []; unmapped modules: []. Current top-five files outside the frozen nine require a separate serial supplemental label; they must not be appended to the paired profile set.

| File | Warm wall (s) | Import | Typeclass | Simp | Elaboration | Type checking | Tactic execution |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `QuantumChannelContinuity/SDPCone.lean` | 87.87 | 55.20 | 24.40 | 2.28 | 0.40 | 0.58 | 1.63 |
| `QuantumChannelContinuity/Schatten.lean` | 86.64 | 53.80 | 101.00 | 5.92 | 4.05 | 4.39 | 18.60 |
| `QuantumChannelContinuity/TensorChannels.lean` | 61.32 | 47.80 | 6.64 | 1.41 | 0.59 | 0.49 | 1.29 |
| `QuantumChannelContinuity/FilterAlignment.lean` | 51.84 | 39.00 | 6.06 | 1.03 | 0.61 | 1.04 | 1.91 |
| `QuantumChannelContinuity/SDPTrace.lean` | 53.93 | 40.70 | 6.82 | 1.36 | 0.25 | 0.68 | 0.46 |
| `QuantumChannelContinuity/SourceCorrespondence.lean` | 40.08 | 29.70 | 2.83 | 0.28 | 0.27 | 0.29 | 1.32 |
| `QuantumChannelContinuity/Filter.lean` | 40.25 | 21.20 | 20.70 | 1.78 | 1.01 | 1.62 | 4.37 |
| `QuantumChannelContinuity/OrderConvexity.lean` | 22.18 | 13.00 | 0.22 | 0.01 | 0.02 | 0.05 | 0.08 |
| `QuantumChannelContinuity/RegularizationSup.lean` | 15.42 | 7.15 | 0.20 | 0.07 | 0.03 | 0.02 | 0.12 |

Phase values are seconds from the flat `--profile` cumulative counters. The pinned Lean `Lean.Util.Profile` documentation calls these **exclusive component execution times**: exclusion applies within an instrumented execution stack. Counters aggregate Lean threads/tasks, whose durations can overlap in wall time, so categories do not partition the GNU wall clock and their wall-time percentages need not total 100%. Their sum is not GNU process CPU or wall time; uninstrumented runtime and rounding can also differ. Structured `trace.profiler` trees are a separate profiler with nested durations that may overlap as well. A dash means that a flat label was absent, not a measured zero. Build elapsed durations and warm serial wall times measure different scopes. `SourceCorrespondence`, when present, is an explicitly additional paired supplemental profile; it is not one of the 83 cold-build modules.

Primary implementation references: [thread-local parent stack, exclusive subtraction and global category accumulation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/library/time_task.cpp), [steady-clock elapsed timer](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/util/timeit.h), and [flat-profiler option documentation](https://github.com/leanprover/lean4/blob/v4.29.0-rc6/src/Lean/Util/Profile.lean). Routing selects the largest qualified counter and lists other qualified counters. The >25%-of-warm-wall screen is a heuristic applied to aggregated timers, not a measured share of a wall-time partition.

**`QuantumChannelContinuity/SDPCone.lean`**: Largest qualified counter: `import` (55.20 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (24.40 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `ab2cca84a5d65809d5cffd93eac986dcb3ddab7e357b37295725d22ded440413`; raw profile SHA256: `a6a678bad4fae9c7f3aa2785330eac70dec5f6ac6b1302ba5f4e6fee8696be77`.

All reported cumulative phases: `{"attribute application": 7.3e-05, "congr simp thm": 0.004070000000000001, "elaboration": 0.401, "fix level params": 0.00615, "import": 55.2, "initialization": 0.038700000000000005, "instantiate metavars": 0.0414, "interpretation": 2.54, "let-to-have transformation": 0.000763, "linting": 0.113, "norm_num": 0.00271, "parsing": 0.0289, "process pre-definitions": 0.0391, "ring": 0.0304, "share common exprs": 0.0222, "simp": 2.28, "tactic execution": 1.63, "type checking": 0.581, "typeclass inference": 24.4}`.

Reported event lines strictly over 100ms: 63 (63 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 55.2s
typeclass inference of ZeroHomClass took 134ms
typeclass inference of AddMonoidWithOne took 127ms
typeclass inference of HSMul took 260ms
typeclass inference of SMul took 195ms
typeclass inference of Semiring took 152ms
typeclass inference of AddCommMonoid took 152ms
typeclass inference of SMul took 691ms
typeclass inference of Semiring took 124ms
typeclass inference of AddCommMonoid took 147ms
typeclass inference of SMul took 578ms
typeclass inference of MulAction took 487ms
typeclass inference of MulAction took 974ms
typeclass inference of AddCommMonoid took 508ms
typeclass inference of MulAction took 750ms
typeclass inference of NonUnitalSemiring took 213ms
typeclass inference of NonUnitalSemiring took 152ms
typeclass inference of MulAction took 922ms
elaboration took 102ms
type checking took 106ms
type checking took 117ms
interpretation of Mathlib.TacticAnalysis.runPass._boxed took 115ms
typeclass inference of SequentialSpace took 106ms
typeclass inference of Module took 107ms
typeclass inference of Module took 175ms
typeclass inference of NormedSpace took 895ms
typeclass inference of ContinuousSMul took 309ms
tactic execution of Lean.Parser.Tactic.refine took 143ms
typeclass inference of Norm took 126ms
typeclass inference of ProperSpace took 817ms
typeclass inference of Module took 163ms
typeclass inference of NormedSpace took 696ms
typeclass inference of ContinuousSMul took 204ms
typeclass inference of Module took 134ms
typeclass inference of NormedSpace took 453ms
typeclass inference of ContinuousSMul took 184ms
tactic execution of Lean.Parser.Tactic.exact took 101ms
type checking took 177ms
elaboration took 193ms
typeclass inference of Module took 233ms
typeclass inference of NormedSpace took 727ms
typeclass inference of Module took 143ms
typeclass inference of NormedSpace took 549ms
typeclass inference of ContinuousSMul took 637ms
typeclass inference of NormedSpace took 1.22s
typeclass inference of LocallyConvexSpace took 155ms
tactic execution of Lean.Parser.Tactic.obtain took 177ms
tactic execution of Lean.Parser.Tactic.refine took 118ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 102ms
typeclass inference of AddHomClass took 192ms
typeclass inference of ZeroHomClass took 249ms
typeclass inference of AddMonoidHomClass took 178ms
typeclass inference of AddMonoidHomClass took 173ms
typeclass inference of ZeroHomClass took 216ms
typeclass inference of ZeroHomClass took 141ms
typeclass inference of Semiring took 169ms
typeclass inference of AddMonoidWithOne took 152ms
typeclass inference of ZeroHomClass took 156ms
simp took 1.12s
simp took 686ms
typeclass inference of AddMonoidHomClass took 123ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_linarith_1._boxed took 121ms
type checking took 126ms
```

**`QuantumChannelContinuity/Schatten.lean`**: Largest qualified counter: `typeclass inference` (101.00 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. Other qualified counters: `import` (53.80 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `15b6bfdfbfea1da59b25aeb2915780a6955a1907175231ab0611d379cce48675`; raw profile SHA256: `82cd0f341345aee54df99a97de928a792f4996e67b66d0f95a0bdbf9733373a2`.

All reported cumulative phases: `{"aesop": 0.944, "attribute application": 0.000634, "compilation (IR)": 0.00608, "compilation (LCNF base)": 0.0077, "compilation (LCNF impure)": 0.00348, "compilation (LCNF mono)": 0.012, "congr simp thm": 0.0987, "dsimp": 0.0745, "elaboration": 4.05, "fix level params": 0.0677, "import": 53.8, "initialization": 0.0322, "instantiate metavars": 0.09129999999999999, "interpretation": 7.04, "let-to-have transformation": 0.00607, "linting": 0.19, "norm_num": 0.153, "parsing": 0.356, "process pre-definitions": 0.428, "ring": 0.871, "share common exprs": 0.215, "simp": 5.92, "tactic execution": 18.6, "type checking": 4.39, "typeclass inference": 101.0}`.

Reported event lines strictly over 100ms: 312 (313 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 53.8s
parsing took 146ms
typeclass inference of Algebra took 142ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 111ms
tactic execution of Lean.Parser.Tactic.change took 167ms
type checking took 251ms
typeclass inference of CoeFun took 110ms
typeclass inference of CoeFun took 203ms
typeclass inference of CoeFun took 131ms
typeclass inference of CoeFun took 157ms
typeclass inference of CoeFun took 114ms
typeclass inference of AddMonoidHomClass took 162ms
simp took 394ms
typeclass inference of CoeFun took 110ms
typeclass inference of CoeFun took 104ms
typeclass inference of Algebra took 138ms
typeclass inference of Algebra took 111ms
typeclass inference of CoeFun took 110ms
typeclass inference of Algebra took 198ms
typeclass inference of Algebra took 336ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 251ms
typeclass inference of NonnegSpectrumClass took 133ms
tactic execution of Lean.Parser.Tactic.exact took 115ms
typeclass inference of Nonempty took 224ms
typeclass inference of AddMonoidHomClass took 111ms
simp took 315ms
type checking took 871ms
type checking took 1.15s
typeclass inference of Algebra took 108ms
typeclass inference of Module took 105ms
typeclass inference of Module took 125ms
typeclass inference of Algebra took 271ms
typeclass inference of Algebra took 449ms
typeclass inference of HPow took 493ms
typeclass inference of Module took 112ms
typeclass inference of Module took 204ms
typeclass inference of Module took 173ms
typeclass inference of Module took 589ms
typeclass inference of Module took 396ms
typeclass inference of Module took 267ms
typeclass inference of NormedSpace took 117ms
typeclass inference of Module took 207ms
typeclass inference of Algebra took 1.46s
typeclass inference of StarOrderedRing took 132ms
typeclass inference of Algebra took 296ms
typeclass inference of ContinuousFunctionalCalculus took 1.19s
typeclass inference of NonnegSpectrumClass took 233ms
typeclass inference of DivisionRing took 107ms
typeclass inference of IsTopologicalRing took 405ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 854ms
typeclass inference of StarRing took 159ms
typeclass inference of TopologicalSpace took 166ms
typeclass inference of Algebra took 728ms
typeclass inference of ContinuousFunctionalCalculus took 113ms
tactic execution of Lean.Parser.Tactic.exact took 149ms
tactic execution of Lean.Parser.Tactic.Conv.rewrite took 209ms
typeclass inference of Algebra took 165ms
typeclass inference of ContinuousFunctionalCalculus took 516ms
typeclass inference of NonnegSpectrumClass took 116ms
typeclass inference of IsTopologicalRing took 102ms
typeclass inference of NeZero took 296ms
typeclass inference of IsScalarTower took 160ms
typeclass inference of Module took 128ms
typeclass inference of Module took 134ms
typeclass inference of Module took 211ms
typeclass inference of Algebra took 309ms
typeclass inference of Algebra took 267ms
typeclass inference of Algebra took 611ms
typeclass inference of NonUnitalContinuousFunctionalCalculus took 157ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 1.49s
type checking took 442ms
typeclass inference of Algebra took 123ms
typeclass inference of Algebra took 262ms
typeclass inference of ContinuousFunctionalCalculus took 320ms
tactic execution of Lean.Parser.Tactic.refine took 203ms
simp took 277ms
typeclass inference of Algebra took 250ms
typeclass inference of ContinuousFunctionalCalculus took 274ms
typeclass inference of NonnegSpectrumClass took 185ms
typeclass inference of IsTopologicalRing took 166ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 388ms
typeclass inference of LE took 281ms
interpretation of Mathlib.Tactic.FieldSimp._aux_Mathlib_Tactic_FieldSimp___elabRules_Mathlib_Tactic_FieldSimp_fieldSimp_1._boxed took 335ms
typeclass inference of Ring took 129ms
typeclass inference of AddCommMonoid took 144ms
typeclass inference of AddCommMonoid took 118ms
typeclass inference of MulAction took 419ms
typeclass inference of Algebra took 1.05s
typeclass inference of ContinuousFunctionalCalculus took 202ms
typeclass inference of NonnegSpectrumClass took 160ms
tactic execution of Lean.Parser.Tactic.refine took 141ms
tactic execution of Lean.Parser.Tactic.change took 112ms
tactic execution of Lean.Parser.Tactic.exact took 131ms
typeclass inference of CoeFun took 504ms
tactic execution of Lean.Parser.Tactic.refine took 201ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 499ms
typeclass inference of CoeFun took 187ms
typeclass inference of AddCommMonoid took 115ms
tactic execution of Lean.Parser.Tactic.congr took 161ms
typeclass inference of CoeFun took 300ms
interpretation of Lean.Elab.Tactic._aux_Mathlib_Tactic_Widget_Calc___elabRules_Lean_calcTactic_1._boxed took 228ms
tactic execution of Lean.Parser.Tactic.rcases took 153ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 103ms
type checking took 257ms
typeclass inference of Algebra took 116ms
typeclass inference of Algebra took 125ms
typeclass inference of Nonempty took 150ms
simp took 178ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 193ms
tactic execution of Lean.Parser.Tactic.exact took 191ms
type checking took 185ms
typeclass inference of Algebra took 125ms
typeclass inference of Algebra took 111ms
typeclass inference of Algebra took 107ms
typeclass inference of ContinuousFunctionalCalculus took 129ms
typeclass inference of Algebra took 147ms
typeclass inference of ContinuousFunctionalCalculus took 205ms
typeclass inference of NonnegSpectrumClass took 101ms
typeclass inference of IsTopologicalRing took 103ms
simp took 177ms
typeclass inference of Algebra took 199ms
typeclass inference of ContinuousFunctionalCalculus took 143ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 254ms
tactic execution of Lean.Parser.Tactic.exact took 258ms
type checking took 148ms
typeclass inference of Algebra took 155ms
typeclass inference of ContinuousFunctionalCalculus took 230ms
elaboration took 102ms
typeclass inference of HSMul took 130ms
typeclass inference of Module took 106ms
typeclass inference of Module took 109ms
typeclass inference of Module took 218ms
typeclass inference of SMulZeroClass took 491ms
typeclass inference of SMulZeroClass took 216ms
typeclass inference of Module took 369ms
typeclass inference of CommMonoid took 124ms
typeclass inference of MulAction took 244ms
typeclass inference of Module took 248ms
typeclass inference of Algebra took 613ms
typeclass inference of Algebra took 235ms
typeclass inference of Algebra took 1.1s
typeclass inference of PosSMulMono took 2.49s
typeclass inference of StarRing took 210ms
typeclass inference of Module took 138ms
typeclass inference of Algebra took 617ms
typeclass inference of ContinuousFunctionalCalculus took 846ms
typeclass inference of NonnegSpectrumClass took 105ms
typeclass inference of DivisionRing took 202ms
typeclass inference of IsTopologicalRing took 179ms
typeclass inference of Algebra took 129ms
typeclass inference of ContinuousFunctionalCalculus took 258ms
typeclass inference of IsTopologicalRing took 131ms
simp took 401ms
tactic execution of Lean.Parser.Tactic.simp took 371ms
typeclass inference of Algebra took 260ms
typeclass inference of ContinuousFunctionalCalculus took 154ms
typeclass inference of ContinuousMap.UniqueHom took 586ms
typeclass inference of SMulZeroClass took 326ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 525ms
typeclass inference of ContinuousFunctionalCalculus took 193ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 298ms
typeclass inference of ContinuousFunctionalCalculus took 165ms
type checking took 149ms
typeclass inference of Algebra took 279ms
typeclass inference of ContinuousFunctionalCalculus took 315ms
elaboration took 120ms
typeclass inference of Algebra took 467ms
typeclass inference of ContinuousFunctionalCalculus took 315ms
typeclass inference of NonnegSpectrumClass took 113ms
typeclass inference of IsTopologicalRing took 142ms
simp took 602ms
typeclass inference of T1Space took 117ms
typeclass inference of StarRing took 178ms
typeclass inference of Module took 149ms
typeclass inference of Module took 113ms
typeclass inference of Algebra took 1.33s
typeclass inference of ContinuousFunctionalCalculus took 335ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 173ms
typeclass inference of Preorder took 309ms
typeclass inference of CanonicallyOrderedAdd took 488ms
simp took 194ms
simp took 103ms
typeclass inference of CommSemiring took 103ms
typeclass inference of CanonicallyOrderedAdd took 353ms
typeclass inference of StarRing took 157ms
typeclass inference of PartialOrder took 112ms
simp took 263ms
typeclass inference of CanonicallyOrderedAdd took 324ms
simp took 221ms
aesop took 944ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 310ms
typeclass inference of Algebra took 132ms
typeclass inference of ContinuousFunctionalCalculus took 237ms
type checking took 127ms
typeclass inference of CoeFun took 171ms
typeclass inference of AddRightMono took 203ms
tactic execution of Lean.Parser.Tactic.refine took 142ms
typeclass inference of AddMonoidHomClass took 163ms
typeclass inference of HSMul took 373ms
typeclass inference of Algebra took 359ms
typeclass inference of ContinuousFunctionalCalculus took 865ms
typeclass inference of Ring took 171ms
typeclass inference of StarOrderedRing took 106ms
typeclass inference of CoeT took 298ms
elaboration took 670ms
typeclass inference of StarRing took 136ms
typeclass inference of Algebra took 369ms
typeclass inference of ContinuousFunctionalCalculus took 205ms
typeclass inference of NonnegSpectrumClass took 499ms
typeclass inference of HSMul took 622ms
typeclass inference of IsOrderedRing took 251ms
ring took 246ms
typeclass inference of IsOrderedRing took 489ms
typeclass inference of CharZero took 154ms
tactic execution of Lean.Parser.Tactic.refine took 613ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 545ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 171ms
typeclass inference of Algebra took 162ms
typeclass inference of Algebra took 157ms
typeclass inference of Algebra took 542ms
typeclass inference of LinearMap.CompatibleSMul took 222ms
type checking took 155ms
typeclass inference of HSMul took 345ms
elaboration took 208ms
typeclass inference of AddCommMonoid took 127ms
typeclass inference of MulAction took 220ms
typeclass inference of Algebra took 931ms
typeclass inference of ContinuousFunctionalCalculus took 461ms
typeclass inference of NonnegSpectrumClass took 266ms
typeclass inference of IsOrderedRing took 332ms
ring took 135ms
typeclass inference of IsOrderedRing took 231ms
tactic execution of Lean.Parser.Tactic.refine took 331ms
typeclass inference of IsOrderedRing took 122ms
tactic execution of Lean.Parser.Tactic.refine took 168ms
typeclass inference of Algebra took 267ms
typeclass inference of ContinuousFunctionalCalculus took 135ms
tactic execution of Lean.Parser.Tactic.simpa took 119ms
typeclass inference of Algebra took 193ms
typeclass inference of ContinuousFunctionalCalculus took 210ms
typeclass inference of NonnegSpectrumClass took 107ms
tactic execution of Lean.Parser.Tactic.refine took 348ms
typeclass inference of CanonicallyOrderedAdd took 221ms
interpretation of Mathlib.Tactic.FieldSimp._aux_Mathlib_Tactic_FieldSimp___elabRules_Mathlib_Tactic_FieldSimp_fieldSimp_1._boxed took 616ms
typeclass inference of Algebra took 218ms
typeclass inference of ContinuousFunctionalCalculus took 218ms
typeclass inference of NonnegSpectrumClass took 192ms
tactic execution of Lean.Parser.Tactic.refine took 124ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 455ms
tactic execution of Mathlib.Tactic.linarith took 197ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 125ms
interpretation of Lean.Elab.Tactic._aux_Mathlib_Tactic_Widget_Calc___elabRules_Lean_calcTactic_1._boxed took 646ms
typeclass inference of HSMul took 112ms
typeclass inference of Module took 125ms
typeclass inference of Algebra took 182ms
typeclass inference of Algebra took 128ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 102ms
typeclass inference of Module took 309ms
typeclass inference of Module took 134ms
typeclass inference of HSMul took 829ms
elaboration took 125ms
tactic execution of Lean.Parser.Tactic.refine took 215ms
typeclass inference of HPow took 102ms
interpretation of Mathlib.Meta.NormNum.evalOfNat._lam_1._boxed took 220ms
interpretation of Mathlib.Meta.NormNum.evalOfNat._lam_1._boxed took 107ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 185ms
typeclass inference of Module took 173ms
typeclass inference of HSMul took 893ms
typeclass inference of LE took 129ms
typeclass inference of CoeFun took 108ms
elaboration took 285ms
tactic execution of Lean.Parser.Tactic.refine took 164ms
typeclass inference of HeytingAlgebra took 137ms
typeclass inference of Nonempty took 471ms
typeclass inference of AddMonoidHomClass took 137ms
typeclass inference of Monoid took 332ms
typeclass inference of AddCommMonoid took 165ms
simp took 649ms
typeclass inference of CoeFun took 369ms
typeclass inference of CoeFun took 243ms
tactic execution of Lean.Parser.Tactic.change took 183ms
typeclass inference of CoeFun took 785ms
typeclass inference of CoeFun took 353ms
typeclass inference of CoeFun took 203ms
typeclass inference of CoeFun took 297ms
typeclass inference of Nonempty took 234ms
typeclass inference of AddMonoidHomClass took 186ms
typeclass inference of SMul took 231ms
simp took 649ms
typeclass inference of CoeFun took 400ms
elaboration took 187ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 274ms
typeclass inference of SeminormedAddCommGroup took 308ms
typeclass inference of InnerProductSpace took 109ms
tactic execution of Lean.Parser.Tactic.exact took 222ms
typeclass inference of CoeFun took 122ms
typeclass inference of HSMul took 283ms
elaboration took 718ms
typeclass inference of NonUnitalNonAssocSemiring took 234ms
typeclass inference of NonUnitalSemiring took 276ms
typeclass inference of AddMonoidHomClass took 524ms
tactic execution of Lean.Parser.Tactic.simpa took 148ms
typeclass inference of CoeFun took 137ms
typeclass inference of HSMul took 240ms
typeclass inference of Module took 128ms
typeclass inference of CoeFun took 361ms
elaboration took 300ms
tactic execution of Lean.Parser.Tactic.simpa took 193ms
typeclass inference of CoeFun took 121ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 221ms
typeclass inference of HSMul took 155ms
elaboration took 160ms
```

**`QuantumChannelContinuity/TensorChannels.lean`**: Largest qualified counter: `import` (47.80 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `e561e8318f2f13c9c3a7773c21ed84e5bfda4adc6bed966aacd38903c40edfa6`; raw profile SHA256: `97283b9f1f85ea4470297d6ed2233066aa0d74015b117790691ce87325f51185`.

All reported cumulative phases: `{"attribute application": 5.98e-05, "blocked (unaccounted)": 0.000716, "congr simp thm": 0.00992, "elaboration": 0.595, "fix level params": 0.00421, "import": 47.8, "initialization": 0.0275, "instantiate metavars": 0.0444, "interpretation": 2.04, "let-to-have transformation": 0.00044500000000000003, "linting": 0.041100000000000005, "parsing": 0.00551, "process pre-definitions": 0.0396, "share common exprs": 0.0112, "simp": 1.41, "tactic execution": 1.29, "type checking": 0.486, "typeclass inference": 6.64}`.

Reported event lines strictly over 100ms: 13 (13 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 47.8s
typeclass inference of ZeroHomClass took 370ms
typeclass inference of Nonempty took 154ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 141ms
simp took 280ms
simp took 135ms
simp took 157ms
simp took 292ms
typeclass inference of ZeroHomClass took 386ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 171ms
typeclass inference of AddHomClass took 104ms
tactic execution of Lean.Parser.Tactic.obtain took 400ms
elaboration took 416ms
```

**`QuantumChannelContinuity/FilterAlignment.lean`**: Largest qualified counter: `import` (39.00 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `eab78d995aec86038f213000a12ebef7bf58effa8a86e757acd27c2a5db787c4`; raw profile SHA256: `f1a3054515efd6bb6a21febdb605a4451b21d1263d4cc6574ca25f6905b4b9c2`.

All reported cumulative phases: `{"attribute application": 0.0032, "congr simp thm": 0.0149, "dsimp": 0.00126, "elaboration": 0.614, "fix level params": 0.0134, "import": 39.0, "initialization": 0.0448, "instantiate metavars": 0.0322, "interpretation": 3.93, "let-to-have transformation": 0.002, "linting": 0.0445, "norm_num": 0.00726, "parsing": 0.0166, "process pre-definitions": 0.0405, "ring": 0.07379999999999999, "share common exprs": 0.0531, "simp": 1.03, "tactic execution": 1.91, "type checking": 1.04, "typeclass inference": 6.06}`.

Reported event lines strictly over 100ms: 17 (18 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 39s
typeclass inference of Add took 152ms
simp took 146ms
typeclass inference of ZeroHomClass took 102ms
typeclass inference of SeminormedAddCommGroup took 193ms
typeclass inference of ZeroHomClass took 216ms
type checking took 182ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 855ms
type checking took 118ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 110ms
tactic execution of Lean.Parser.Tactic.change took 200ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 129ms
simp took 241ms
tactic execution of Lean.Parser.Tactic.obtain took 146ms
tactic execution of Lean.Parser.Tactic.exact took 359ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 778ms
type checking took 133ms
```

**`QuantumChannelContinuity/SDPTrace.lean`**: Largest qualified counter: `import` (40.70 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `2a9a58e75c92968a666b8e890e88e031baf8f14885ee51c010a36c90c2b26f84`; raw profile SHA256: `25a3e75c7797e89d23e89a22cd9182c4867d1b0f2d37bbf5a6456ba667b421da`.

All reported cumulative phases: `{"attribute application": 0.00885, "congr simp thm": 0.0061200000000000004, "elaboration": 0.246, "fix level params": 0.00365, "import": 40.7, "initialization": 0.0431, "instantiate metavars": 0.00491, "interpretation": 2.38, "let-to-have transformation": 0.00744, "linting": 0.054700000000000006, "parsing": 0.011699999999999999, "process pre-definitions": 0.0546, "share common exprs": 0.0109, "simp": 1.36, "tactic execution": 0.456, "type checking": 0.678, "typeclass inference": 6.82}`.

Reported event lines strictly over 100ms: 15 (15 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 40.7s
typeclass inference of Module took 243ms
typeclass inference of StarModule took 215ms
simp took 320ms
simp took 431ms
typeclass inference of FiniteDimensional took 104ms
typeclass inference of Semiring took 148ms
simp took 458ms
typeclass inference of HSMul took 247ms
typeclass inference of HSMul took 254ms
typeclass inference of Semiring took 160ms
typeclass inference of AddCommMonoid took 150ms
typeclass inference of DistribSMul took 306ms
typeclass inference of DistribSMul took 284ms
typeclass inference of AddMonoidHomClass took 157ms
```

**`QuantumChannelContinuity/SourceCorrespondence.lean`**: Largest qualified counter: `import` (29.70 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `1319b701c9fc33fd4ab8b36720b0bbf7909a7e4f61888c29752b8b93810ee2ef`; raw profile SHA256: `d1fae789b5118daddfae0ad2dd01675f6ee0d74f5c52ae3b9644c42be30b5be4`.

All reported cumulative phases: `{"attribute application": 0.00011999999999999999, "congr simp thm": 0.00767, "elaboration": 0.271, "fix level params": 0.00184, "import": 29.7, "initialization": 0.047200000000000006, "instantiate metavars": 0.00872, "interpretation": 2.62, "let-to-have transformation": 0.00062, "linting": 0.015, "parsing": 0.0134, "process pre-definitions": 0.018, "share common exprs": 0.0112, "simp": 0.277, "tactic execution": 1.32, "type checking": 0.295, "typeclass inference": 2.83}`.

Reported event lines strictly over 100ms: 10 (10 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 29.7s
typeclass inference of CoeFun took 113ms
tactic execution of Lean.Parser.Tactic.change took 243ms
simp took 107ms
tactic execution of Lean.Parser.Tactic.obtain took 132ms
typeclass inference of ZeroHomClass took 361ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 356ms
typeclass inference of AddHomClass took 203ms
type checking took 140ms
tactic execution of Lean.Parser.Tactic.exact took 267ms
```

**`QuantumChannelContinuity/Filter.lean`**: Largest qualified counter: `import` (21.20 s) — consumer import narrowing candidate; no local-proof cause inferred. Other qualified counters: `typeclass inference` (20.70 s) — typeclass trace needed to distinguish named expensive searches from a diffuse floor before proposing caches. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `b2ee2c121040b52b943264d6263117447bf672dfb1de6da4516668754ff395c5`; raw profile SHA256: `180d1de89a766862e7bb352a7d1f9a86a508738b5595e2d4939f752e1556ed8e`.

All reported cumulative phases: `{"attribute application": 0.000335, "congr simp thm": 0.013099999999999999, "elaboration": 1.01, "fix level params": 0.0185, "import": 21.2, "initialization": 0.133, "instantiate metavars": 0.0395, "interpretation": 4.96, "let-to-have transformation": 0.00387, "linting": 0.0831, "norm_num": 0.026600000000000002, "parsing": 0.0288, "process pre-definitions": 0.061200000000000004, "ring": 0.07540000000000001, "share common exprs": 0.0557, "simp": 1.78, "tactic execution": 4.37, "type checking": 1.62, "typeclass inference": 20.7}`.

Reported event lines strictly over 100ms: 48 (49 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 21.2s
typeclass inference of CoeT took 270ms
typeclass inference of HSMul took 107ms
typeclass inference of AddMonoidHomClass took 177ms
simp took 281ms
typeclass inference of CoeFun took 126ms
simp took 252ms
simp took 295ms
tactic execution of Lean.Parser.Tactic.simpa took 343ms
type checking took 211ms
simp took 103ms
tactic execution of Lean.Parser.Tactic.change took 184ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 183ms
typeclass inference of CoeFun took 170ms
elaboration took 127ms
typeclass inference of CoeFun took 128ms
tactic execution of Lean.Parser.Tactic.refine took 204ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 292ms
typeclass inference of CoeFun took 104ms
typeclass inference of CoeFun took 133ms
tactic execution of Lean.Parser.Tactic.exact took 136ms
typeclass inference of CoeFun took 107ms
typeclass inference of CoeFun took 114ms
tactic execution of Lean.Parser.Tactic.exact took 140ms
typeclass inference of ZeroHomClass took 378ms
tactic execution of Lean.Parser.Tactic.simpa took 210ms
typeclass inference of AddHomClass took 186ms
type checking took 501ms
typeclass inference of CoeFun took 222ms
type checking took 104ms
typeclass inference of CoeFun took 234ms
typeclass inference of CoeFun took 106ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 187ms
typeclass inference of CoeFun took 115ms
typeclass inference of CoeFun took 109ms
typeclass inference of Module took 197ms
typeclass inference of Algebra took 107ms
typeclass inference of Module took 143ms
typeclass inference of Algebra took 108ms
typeclass inference of CoeFun took 105ms
tactic execution of Lean.Parser.Tactic.obtain took 125ms
simp took 170ms
tactic execution of Lean.Parser.Tactic.rewriteSeq took 109ms
tactic execution of Lean.Parser.Tactic.exact took 244ms
tactic execution of Lean.Parser.Tactic.obtain took 110ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_nlinarith_1._boxed took 2.02s
type checking took 121ms
typeclass inference of CoeFun took 113ms
```

**`QuantumChannelContinuity/OrderConvexity.lean`**: Largest qualified counter: `import` (13.00 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `cc10d02a4608b1c890051575961d53818de5a6e4521a6f5585186811e64de935`; raw profile SHA256: `ef2b0af828e402a4c5d30845b7e49b63b531a6d2b81f120550c333cd286a3cdd`.

All reported cumulative phases: `{"attribute application": 4.3299999999999995e-05, "blocked (unaccounted)": 0.0008110000000000001, "congr simp thm": 0.0007880000000000001, "elaboration": 0.0166, "fix level params": 0.00047, "import": 13.0, "initialization": 0.053, "instantiate metavars": 0.000509, "interpretation": 1.71, "let-to-have transformation": 8.89e-05, "linting": 0.00813, "norm_num": 0.276, "parsing": 0.00312, "process pre-definitions": 0.00483, "ring": 0.0693, "share common exprs": 0.0058200000000000005, "simp": 0.0103, "tactic execution": 0.0773, "type checking": 0.046200000000000005, "typeclass inference": 0.223}`.

Reported event lines strictly over 100ms: 3 (3 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 13s
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_linarith_1._boxed took 111ms
interpretation of Mathlib.Tactic._aux_Mathlib_Tactic_Linarith_Frontend___elabRules_Mathlib_Tactic_linarith_1._boxed took 106ms
```

**`QuantumChannelContinuity/RegularizationSup.lean`**: Largest qualified counter: `import` (7.15 s) — consumer import narrowing candidate; no local-proof cause inferred. These are routing screens, not a partition of wall-clock time. Exit: 0; dependency artifacts unchanged: True. Source SHA256: `7dbe59ae3c10cea71fba827bd40fb016ef2b0eb00b98c865a55bf24d24d2dbbf`; raw profile SHA256: `9c5329fbcdf4361d88ac26aeaa09b57d9531e53cc00002752796fcb9e6da29c1`.

All reported cumulative phases: `{"attribute application": 5.28e-05, "compilation (IR)": 0.000184, "compilation (LCNF base)": 0.0019299999999999999, "compilation (LCNF impure)": 0.00038500000000000003, "compilation (LCNF mono)": 0.00113, "congr simp thm": 0.0014399999999999999, "elaboration": 0.0332, "fix level params": 0.000182, "import": 7.15, "initialization": 0.0665, "instantiate metavars": 0.000446, "interpretation": 2.17, "let-to-have transformation": 0.000215, "linting": 0.00677, "parsing": 0.006860000000000001, "process pre-definitions": 0.0023799999999999997, "share common exprs": 0.00156, "simp": 0.0706, "tactic execution": 0.123, "type checking": 0.023600000000000003, "typeclass inference": 0.203}`.

Reported event lines strictly over 100ms: 1 (1 raw duration lines parsed). This is not necessarily a count of unique calls, and sub-100ms events are not comprehensively exposed by Lean.

```text
import took 7.15s
```

## 8. Findings ranked by actionability

Separate supplemental current top-five selection complete: **True**. Supplemental input SHA256: `4f10d8b13a0f40ddfecec2a3477793a832524a126660cc57af42a5935b4ea6ee`. These unpaired diagnostics do not change the nine-file comparison gate.

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
- [Metrics evidence](docs/elaboration/after/metrics.json)
- [Warm profile evidence](docs/elaboration/after/profiles.json)
- [Prior clean baseline report](ELABORATION_REPORT_2026-10-06_BEFORE.md)
- [Before/after comparison](docs/elaboration/COMPARISON_2026-10-06.md)
