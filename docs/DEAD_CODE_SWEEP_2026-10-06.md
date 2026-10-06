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

No tracked Lean module imports these files. They define no mathematical declarations. Their 52 diagnostic commands currently compile under the `QuantumChannelContinuity` library glob. The root [Audit.lean](../Audit.lean), now also importing the supplementary source-correspondence module, checks the transitive axioms of all loaded project declarations, including private helpers and proof fields; moving these extra diagnostics preserves named inspection without treating it as ordinary proof-library elaboration.

## Retained deliberately

- `FiniteAnalyticInputs`, `RemainingFiniteInputs`, `QuantumThresholdInputs`, their constructors and right-continuity bridge are **live** dependencies of `theorem_one`. Their record fields are constructed inside the proof, rather than left as premises of the final result.
- The concrete support-mismatch theorem and its normalized input lemma remain as standalone mathematical results.
- Matrix sandwich identities, scalar testing bounds, threshold identities, state-order special cases and tensor lemmas remain reusable APIs even when no certified target currently uses a terminal result.
- `SourceCorrespondence` supplies a supplementary paper-to-Lean tensor-order bridge.
- Comparator challenges, intentional negative controls, the root axiom audit and index/check scripts remain verification tools.

## Import candidates and verification boundary

`ChannelContinuity/Main.lean` has no direct expression dependency on `ChannelContinuity.OperatorAlgebra` or `ChannelContinuity.Testing`. Testing is independently imported by `FoundationsTesting`. If these imports are removed from the scalar consumer, preserve the matrix API in the `ChannelContinuity.lean` facade and validate the full build: expression graphs do not capture every elaboration-time instance dependency. This audit therefore does not claim import removal has been proved safe solely by the graph.

After the sweep, rebuild all project libraries, regenerate the index and current-source metadata, run the exhaustive axiom audit and Comparator regression checks, and confirm the three certified theorem signatures remain unchanged. Historical release certificates must retain their historical source hashes; they must not silently be presented as certificates for modified files.

The machine-readable [evidence record](elaboration/dead-code-sweep.json) contains the full declaration names, exact source ranges, reverse-user lists, graph snapshot hash and retain decisions. No performance improvement is claimed by this audit; elaboration measurements begin only after this sweep.
