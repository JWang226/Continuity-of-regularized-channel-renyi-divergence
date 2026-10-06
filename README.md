# Continuity of regularized channel Rényi divergence

Lean 4 proof of Theorem 1 in [**Continuity of Regularized Channel Rényi
Divergences**](https://arxiv.org/abs/2609.28635), by Jinzhao Wang and Yuxiang Yang.
Developed with assistance from Codex.

[Proof map](docs/PROOF_MAP.md) · [Statement audit](docs/STATEMENT_AUDIT.md) ·
[Verification guide](VERIFYING.md)

## The statements

| Result | Checked declaration | Conclusion |
| --- | --- | --- |
| Theorem 1: continuity | [`theorem_one`](QuantumChannelContinuity/Main.lean) | Regularized, stabilized sandwiched Rényi channel divergence tends to regularized relative entropy as the order approaches one from both sides. |
| Rényi regularization | [`blockRenyi_tendsto_regularized`](QuantumChannelContinuity/RegularizationLimits.lean) | For each fixed order α ≥ ½, α ≠ 1, normalized block divergence converges to its positive-block supremum. |
| Relative-entropy regularization | [`blockRelative_tendsto_regularized`](QuantumChannelContinuity/RegularizationLimits.lean) | Normalized relative entropy of channel tensor powers converges to its positive-block supremum. |

All three statements allow infinite divergence and apply to CPTP channels between
nonzero finite-dimensional complex Hilbert spaces. The continuity theorem has
no additional quantum-information hypotheses. The block identities connect
Lean's supremum definitions to the paper's asymptotic limits.

The declarations are in the `QuantumChannelContinuity` namespace. The
[paper-to-Lean mapping](docs/paper-mapping.json) records supporting results and
their scope; the paper's later operational corollaries are outside this formalization.

## How it was verified

- **Lean:** the build and transitive axiom audit passed for 1,327 project
  declarations, including 1,101 theorems. Only `propext`, `Classical.choice`, and
  `Quot.sound` are permitted; the proof library has no unresolved placeholders
  or project-specific axioms.
- **Comparator:** compared all three statements and referenced definitions
  against the [separate challenge](ComparatorChallenges/ChannelRenyiContinuity.lean),
  checked axioms, and replayed the proofs through Lean's kernel. Both the
  wrong-statement and missing-proof controls were rejected. The challenge's
  deliberate specification holes are excluded from the proof library.
- **Nanoda:** the independently implemented Rust kernel accepted 61,851
  declarations in the historical solution export, including all three theorem targets.

The [recorded evidence](Verification/README.md) and
[v1.0.0 certificate archive](https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/tag/v1.0.0)
describe completed local, unsandboxed runs. The certificate is unsigned, and the
Comparator reference was recorded after proof development. Independent human
review of correspondence to the paper remains outstanding. The
[current source record](Verification/current-source-identity.json) verifies that
the 82 historical proof files differ only by added copyright comments.

## Check it yourself

Use macOS or Linux, Git, Python 3.9+, native C/C++ build tools, and
[elan](https://github.com/leanprover/elan). On macOS, install Xcode Command Line
Tools. Initial setup needs internet access and several GB of disk space.
Nanoda reuses Rust/Cargo if available, or installs Rust locally.

If Lean is not installed, first run:

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

Then clone and reproduce the three verification layers:

```sh
git clone https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence.git
cd continuity-of-regularized-channel-renyi-divergence
./run-lake.sh exe cache get
./check.sh             # Build and transitive axiom audit
./check-comparator.sh  # Statement comparison, Lean replay, and rejection controls
./check-nanoda.sh      # Independent kernel check of a fresh proof export
```

For an existing checkout, run the last four commands. Success ends with
`AUDIT PASSED`, `COMPARATOR CHECK PASSED`, and `NANODA CHECK PASSED`, respectively.
Each checker exits nonzero on failure. Fresh logs are saved to `.lake/check.log`,
`.lake/comparator-check/`, and `.lake/nanoda-check/`.

Lean and dependencies are pinned in [lean-toolchain](lean-toolchain) and
[lake-manifest.json](lake-manifest.json). Keep those pins when reproducing the
proof. The [verification guide](VERIFYING.md) gives expected outputs,
troubleshooting, and instructions for replaying the exact released certificate.
The Comparator reproducer uses unsandboxed development mode.

## Read the proof

Start with the [proof map](docs/PROOF_MAP.md), then follow the
[Lean entry point](ChannelRenyiContinuity.lean). The
[declaration index](docs/proof-index.json) records elaborated types and
dependencies. Search lemma descriptions and inspect dependencies locally:

```sh
./search-lemmas.sh "slack attainment"
./search-lemmas.sh --deps QuantumChannelContinuity.theorem_one
```

The [blind Lean read-back](docs/LEAN_READBACK.md) and
[paper comparison](docs/PAPER_COMPARISON.md) explain the definitions and
representation identifications. These are agent-generated review aids.
The [statement audit](docs/STATEMENT_AUDIT.md) adds an explicit Lean proof that
the two tensor-factor conventions agree. Reproduce its checks with
`python3 scripts/check-statement-audit.py`. A reusable trace-power derivative
is prepared as a [Physlib patch](Contributions/Physlib/README.md).
Validate artifact hashes and mappings with `python3 scripts/check-artifacts.py`;
this checks metadata consistency only. The proof map explains index regeneration.

[Formalization metadata](formalization.yaml) · [Paper mappings](docs/paper-mapping.json) ·
[Apache-2.0 license](LICENSE) · [Third-party attribution](THIRD_PARTY.md).
Cite the paper and record the commit checked.
