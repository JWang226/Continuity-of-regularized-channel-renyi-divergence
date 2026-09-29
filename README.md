# Continuity of regularized channel Rényi divergence

Lean formalization of Theorem 1 in **Continuity of Regularized Channel Rényi
Divergences**, by Jinzhao Wang and Yuxiang Yang
([arXiv:2609.28635](https://arxiv.org/abs/2609.28635)).

The theorem proves that regularized, stabilized sandwiched Rényi channel
divergence converges to regularized relative entropy as the order tends to one.
It covers the two-sided limit, including infinite divergence, with no additional
quantum-information hypotheses.

## Proof

The entry point is [ChannelRenyiContinuity.lean](ChannelRenyiContinuity.lean).
The main result, [`QuantumChannelContinuity.theorem_one`](QuantumChannelContinuity/Main.lean), is:

```lean
variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

theorem theorem_one (N M : CPTP H K) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M))
```

The [block-limit identities](QuantumChannelContinuity/RegularizationLimits.lean)
connect the formal definitions to the paper's regularization limits.
The paper's later operational corollaries are outside this formalization's scope.

## Build and check

Requires Git and native build tools (Xcode Command Line Tools on macOS).
If Lean is not installed, first install [elan](https://github.com/leanprover/elan):

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

Then clone and check the proof:

```sh
git clone https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence.git
cd continuity-of-regularized-channel-renyi-divergence
./run-lake.sh exe cache get
./check.sh
```

For an existing checkout, run the last two commands. Lean and dependency versions
are pinned; Lean downloads automatically on first use.

Success ends with **`AUDIT PASSED`**: 1,327 declarations checked using only
`propext`, `Classical.choice`, and `Quot.sound`. The proof contains no `sorry`.
The log is saved to `.lake/check.log`.

## Verification certificate

Comparator checked the main theorem and both block-limit identities against a
separate formal reference and replayed the proofs in Lean's kernel. Independent
nanoda replay accepted **61,851 declarations**; both rejection controls behaved
as expected.

Reproduce either check from this checkout (Python 3.9+ required):

```sh
./check-comparator.sh  # Statement comparison, Lean replay, and rejection controls
./check-nanoda.sh      # Independent Nanoda kernel check of a fresh proof export
```

Both scripts prepare pinned tools and check all three targets. Each saves fresh
logs and `result.json` under `.lake/comparator-check/` or `.lake/nanoda-check/`.
Comparator uses unsandboxed development mode. Nanoda builds its checker from
source and installs Rust locally if Cargo is unavailable.

- [Verification guide](VERIFYING.md): commands, prerequisites, expected outputs,
  checksums, and troubleshooting for reproducing every check.
- [v1.0.0 release](https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/tag/v1.0.0):
  certificate, proof exports, logs, and replay scripts.
- [Verification record](Verification/README.md) and
  [Comparator reference](ComparatorChallenges/README.md).

The certificate is an unsigned local record from an unsandboxed macOS run.
The reference was written after proof development; correspondence to the paper
still requires mathematical review.

## Attribution

[Apache-2.0](LICENSE). See [formalization metadata](formalization.yaml) and
[third-party attribution](THIRD_PARTY.md). Repository layout follows
[openai/ten-proofs](https://github.com/openai/ten-proofs).
