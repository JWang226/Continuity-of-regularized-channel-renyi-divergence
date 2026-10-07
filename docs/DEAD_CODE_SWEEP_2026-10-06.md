<!-- Copyright (c) 2026 Jinzhao Wang. Released under Apache 2.0; see LICENSE. -->
# Dead-code sweep — 2026-10-06

The sweep removed **seven declarations**, including one private helper, and moved **three diagnostic-only modules** outside the proof library. The three certified statements and reusable mathematical results remain intact. The changes precede the first elaboration measurement. A second agent confirmed that the removal set is closed, all three target signatures are byte-identical, and the moved files are unchanged. Build validation is recorded in the elaboration snapshots and fresh verification record.

## Snapshot and method

The audited commit is `c1042369444d325216ef75e2c7cf866580e2035b`. The baseline proof index, preserved in the [source snapshot](../Verification/source-snapshots/pre-cleanup-2026-10-06.zip), contains 1,288 project declarations and 1,067 theorems from the `ChannelRenyiContinuity` import closure. Its three target closures contain 869, 174 and 258 declarations respectively. There are 405 declarations outside every target closure; this is **not** a removal list.

The audit inspected actual Lean expression dependencies and reverse users, then searched all project Lean sources and manual documentation. It did not compile Lean, edit proof sources or mutate build artifacts. The supplementary `SourceCorrespondence` module is intentionally outside the indexed root; its source and purpose were checked separately. Historical certificate/source-hash records are provenance references, not consumers of mathematical declarations.

## Closed removal set

Line ranges below refer to the audited commit and include attached documentation where applicable. Deleting the set together removes every known internal consumer of the five superseded theorem wrappers.

| Declaration | File | Delete block | Expression evidence |
|---|---|---:|---|
| `ChannelContinuity.theorem_one_finite` | `ChannelContinuity/Main.lean` | 134–152 | Only proof user: `theorem_one_conditional` |
| `ChannelContinuity.theorem_one_conditional` | `ChannelContinuity/Main.lean` | 154–169 | No type or proof users |
| `QuantumChannelContinuity.theorem_one_concrete_finite_conditional` | `QuantumChannelContinuity/ConcreteMain.lean` | 103–117 | Only proof users: the following two wrappers |
| `QuantumChannelContinuity.theorem_one_concrete_conditional` | `QuantumChannelContinuity/ConcreteMain.lean` | 166–183 | No type or proof users |
| `QuantumChannelContinuity.theorem_one_from_quantum_inputs` | `QuantumChannelContinuity/QuantumMain.lean` | 142–152 | No type or proof users |
| `QuantumChannelContinuity.quantumThresholdInputs` | `QuantumChannelContinuity/Main.lean` | 45–49 | No type or proof users; the proof calls `quantumThresholdInputs_of_mono` |
| Private `OrderBoundary.rpow_conj_nonneg` | `QuantumChannelContinuity/StateOrderApprox.lean` | 34–38 | No type/proof users; only textual occurrence is its declaration |

All seven have empty target reachability. None is named in the manual proof map, paper mapping or curated lemma descriptions. They comprise 89 source lines including attached comments, before optional blank-line cleanup. Removing the private helper also removes an unused positivity assumption `_hσ`.

The five theorem wrappers describe earlier conditional formulations of Theorem 1; the final theorem has already superseded them. This is an internal repository API cleanup. An unknown external consumer could still use an old public name; the historical commit preserves those names.

## Diagnostic modules

Move these files to `scripts/audits/` and preserve their commands for explicit use with `./run-lake.sh env lean scripts/audits/<file>`:

| File | Lines | `#print axioms` commands |
|---|---:|---:|
| `FoundationsAudit.lean` | 33 | 21 |
| `StateOrderInterpolationAudit.lean` | 35 | 27 |
| `StateSupportLimitsAudit.lean` | 11 | 4 |

No tracked Lean module imports these files. They define no mathematical declarations. Inspection of the installed Lake `LeanLibConfig` showed that default library globs are `roots.map Glob.one`: they select root modules, rather than every source file under the library directory. These three files were therefore already outside ordinary facade builds before the move. Relocating their 52 diagnostic commands is an **organizational change**, preserving explicit named inspection; it does not remove diagnostic work from a previously measured build. This corrects the initial audit's mistaken submodule-glob assumption.

The root [Audit.lean](../Audit.lean), now also importing the supplementary source-correspondence module, checks the transitive axioms of all loaded project declarations, including private helpers and proof fields. Both timed snapshots use the same 83-module facade closure. The complete tree contains 81 solution/support library modules and three Comparator specification/control modules, plus five explicitly run audit/scripts. `SourceCorrespondence` is the one solution/support module outside the timed closure; paired direct profiles and the final full check cover it separately.

## Retained deliberately

- `FiniteAnalyticInputs`, `RemainingFiniteInputs`, `QuantumThresholdInputs`, their constructors and right-continuity bridge are **live** dependencies of `theorem_one`. Their record fields are constructed inside the proof, rather than left as premises of the final result.
- The concrete support-mismatch theorem and its normalized input lemma remain as standalone mathematical results.
- Matrix sandwich identities, scalar testing bounds, threshold identities, state-order special cases and tensor lemmas remain reusable APIs even when no certified target currently uses a terminal result.
- `SourceCorrespondence` supplies a supplementary paper-to-Lean tensor-order bridge.
- Comparator challenges, intentional negative controls, the root axiom audit and index/check scripts remain verification tools.

## Import candidates and verification boundary

`ChannelContinuity/Main.lean` has no direct expression dependency on `ChannelContinuity.OperatorAlgebra` or `ChannelContinuity.Testing`. Testing is independently imported by `FoundationsTesting`. If these imports are removed from the scalar consumer, preserve the matrix API in the `ChannelContinuity.lean` facade and validate the full build: expression graphs do not capture every elaboration-time instance dependency. This audit therefore does not claim import removal has been proved safe solely by the graph.

After the sweep, rebuild the facade libraries and explicitly include the supplementary `SourceCorrespondence` module in the final full check, regenerate the index and current-source metadata, run the exhaustive axiom audit and Comparator regression checks, and confirm the three certified theorem signatures remain unchanged. Historical release certificates must retain their historical source hashes; they must not silently be presented as certificates for modified files.

The machine-readable [evidence record](elaboration/dead-code-sweep.json) contains the full declaration names, exact source ranges, reverse-user lists, graph snapshot hash and retain decisions. No performance improvement is claimed by this audit; elaboration measurements begin only after this sweep.

## Final declaration-index reconciliation

The regenerated index contains **1,268 declarations and 1,047 theorems**, compared with **1,288 and 1,067** in the exact archived index. The difference is **24 removed and four added**: seven named sweep declarations, two generated simp lemmas from a deleted wrapper, and 15 generated proof auxiliaries disappear; the private `hermitianRealModule` cache and its three generated proof auxiliaries appear. Thus **1,288 − 7 − 2 − 15 + 1 + 3 = 1,268**. The 15 cache-related auxiliaries are elaborator artifacts, rather than 15 further deleted source theorems. Downstream `SDPCone.lean` and `SDPPartialTrace.lean` have unchanged source hashes. Exact names, types and category counts are in [declaration-delta.json](elaboration/declaration-delta.json).

All 794 shared non-internal declarations retain identical printed types. All three targets retain identical printed types and direct type/proof dependencies. The main target closure changes **869 → 858** through 15 removed generated auxiliaries and four cache declarations; the two block-limit closures remain **174** and **258**. Eighteen retained internal proof names have different printed types as generated numbering compacts. Two retained `congr_simp` declarations, `inputRelative.congr_simp` and `inputRenyi.congr_simp`, are attributed to `ContinuityAssembly` instead of `ConcreteMain`, with unchanged names and types. These metadata comparisons supplement the verification checks; they do not replace kernel or Comparator validation.

The index still covers the same **75 defining modules** loaded through `ChannelRenyiContinuity`; its extractor, generator, targets, toolchain and dependency pins are unchanged. **1,268 is the indexed root scope, not the count of every owned declaration.** Both indexes exclude supplementary `SourceCorrespondence` and diagnostic-only audit modules. The source-hash inventory changes **83 → 81 file/config paths** because three audits moved outside the scanned directories and the existing supplemental file is now hashed. Hashing that file does not add its declarations to the index; the full axiom audit covers it separately.

The comparison binds these exact bytes:

- Archived ZIP SHA256: `7e50fd557d5992c00311db0855de653b06810d6b994f58623f40900d4513ead2`.
- ZIP member `docs/proof-index.json` SHA256: `1016762b8c0e78263a84e8c6d368480ce38e8f0b2dc6dd3d60e19409d993d244`.
- Regenerated [proof index](proof-index.json) SHA256: `c7f581fcc6c2bb79959ec0cb3fd2d8396d6382f54e18eef50b5b6e0626797850`, for mathematical source commit `8765c21753175381a57b29fa9469b35675515b2c`.
