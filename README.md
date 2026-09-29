# Continuity of regularized channel Rényi divergence

A Lean formalization of Theorem 1 in **Continuity of Regularized Channel Rényi
Divergences**, by Jinzhao Wang and Yuxiang Yang. Read the paper on
[arXiv:2609.28635](https://arxiv.org/abs/2609.28635).

For every pair of finite-dimensional quantum channels, the regularized,
stabilized sandwiched Rényi divergence converges to the regularized channel
relative entropy as the Rényi order tends to one. The formalization covers the
two-sided limit and infinite divergence. The final theorem has no additional
quantum-information or analytic hypotheses.

## Result

[ChannelRenyiContinuity.lean](ChannelRenyiContinuity.lean) imports the completed
proof. Its main declaration is
[`QuantumChannelContinuity.theorem_one`](QuantumChannelContinuity/Main.lean):

```lean
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

theorem theorem_one (N M : CPTP H K) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M))
```

The divergences are valued in `ℝ≥0∞` and measured in bits. The two
[`block-limit identities`](QuantumChannelContinuity/RegularizationLimits.lean)
prove that the positive-block suprema used in the definitions equal the
normalized block limits in the manuscript. Later operational corollaries of
the manuscript are outside the scope of this repository.

## Building

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build All
```

The toolchain and dependencies are pinned in `lean-toolchain` and
`lake-manifest.json`. The proof uses Lean `v4.29.0-rc6`, mathlib, and
[Lean-Quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum).

To build all project modules and audit their transitive axiom dependencies:

```sh
./check.sh
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`. The
completed proof contains no `sorry` or additional axioms. Deliberate holes in
the separate Comparator reference and missing-proof control are excluded from
the proof library.

## Independent checking

See [ComparatorChallenges](ComparatorChallenges/README.md) for comparison
against a separate statement and definitions, Lean kernel replay, independent
nanoda checking, and negative controls. The recorded original check passed for
the main theorem and both block-limit identities; nanoda accepted **61,851
declarations**. The historical audit checked **1,327 project declarations**,
including **1,101 theorem declarations**.

[Verification](Verification/README.md) records the evidence and the identity of
the published mathematical source. The replayable proof exports and
certificate are distributed as
[release assets](https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/tag/v1.0.0)
to keep the Git history small.

This is an unsigned local verification record. The original run used
Comparator's macOS development launcher without Linux sandbox isolation, and
the reference was recorded after proof development. Formal checking verifies
the recorded Lean statements; correspondence to the manuscript also requires
mathematical review.

## Attribution

This repository follows the presentation of
[openai/ten-proofs](https://github.com/openai/ten-proofs). Formalization metadata,
scope, and AI assistance are recorded in [formalization.yaml](formalization.yaml).
See [THIRD_PARTY.md](THIRD_PARTY.md) for dependency licenses and adapted proofs.
The code is released under [Apache-2.0](LICENSE).
