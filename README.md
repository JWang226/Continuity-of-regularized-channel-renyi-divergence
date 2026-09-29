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

## Check the proof yourself

There are three useful checks. You can build the Lean source and audit its
axioms, independently replay the retained proof certificate with nanoda, or
reproduce the full Comparator check and its rejection tests. The commands below
use a macOS or Linux terminal and do not require the author's local files.

### 1. Build the Lean proof and audit its axioms

Install Git, native build tools (Xcode Command Line Tools on macOS, or C/C++
build tools on Linux), and [elan](https://github.com/leanprover/elan#installation).
Open a terminal where `lake --version` works, then run:

```sh
git clone https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence.git
cd continuity-of-regularized-channel-renyi-divergence
./run-lake.sh exe cache get
./check.sh
```

`check.sh` builds the proof and separate Comparator challenge modules, then
audits the transitive axiom dependencies of every project declaration in the
proof library. Success means exit status zero and this line in the output:

```text
AUDIT PASSED: 1327 project declarations, 1101 theorems; transitive axioms [propext, Quot.sound, Classical.choice].
```

The build/audit log is saved as `.lake/check.log`. To build just the main proof,
use `./run-lake.sh build All`. The completed proof contains no `sorry` or extra
axioms. Warnings about `sorry` in `ComparatorChallenges` are expected: the
reference and missing-proof control contain deliberate holes, and neither is
imported by the actual solution or its axiom audit.

The toolchain and dependency commits are pinned in `lean-toolchain` and
`lake-manifest.json`: Lean `v4.29.0-rc6`, mathlib, and
[Lean-Quantum](https://github.com/Hayata-Yamasaki-Group/lean-quantum).
Keep those pins when reproducing this result; do not upgrade the dependencies.
The first build needs network access and several GB of disk space for tools
and dependencies. For the source snapshot associated with the certificate,
run `git checkout v1.0.0` before building.

### 2. Download and independently check the proof certificate

The [v1.0.0 release](https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/tag/v1.0.0)
contains `theorem1-public-verification.zip` (about 136 MiB) and its `.sha256`
file. The archive includes proof exports, the historical certificate, original
source, logs, and reproduction scripts. A JSON report or matching checksum
alone does not check a mathematical proof; the kernel replay below does.

In a directory where you want to keep the download, run:

```sh
release_url=https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/download/v1.0.0
curl -fL "$release_url/theorem1-public-verification.zip" -o theorem1-public-verification.zip
curl -fL "$release_url/theorem1-public-verification.zip.sha256" -o theorem1-public-verification.zip.sha256
shasum -a 256 -c theorem1-public-verification.zip.sha256
unzip theorem1-public-verification.zip
cd theorem1-public-verification
shasum -a 256 -c PUBLIC-SHA256SUMS
```

On Linux, `sha256sum -c FILE` can replace `shasum -a 256 -c FILE`. Every
listed file should report `OK`; stop if a check fails. The archive SHA-256 is:

```text
3b79b882c546956f4a1e8bd61247438e19a9332b2301ee75e234d4bd676fc07b
```

From that extracted `theorem1-public-verification` directory, run:

```sh
cd comparator-verification
./bootstrap-nanoda.sh
gzip -dc exports/Solution.ndjson.gz > exports/Solution.ndjson
python3 run-nanoda.py exports/Solution.ndjson
```

This needs Python 3.9 or newer, Git, curl, gzip, and native build tools. The
bootstrap script builds the pinned nanoda checker from upstream source. It
uses an existing Rust/Cargo installation, or installs Rust 1.98.1 locally in
`.tools` when Cargo is absent. If an existing Rust compiler is too old, select
Rust 1.98.1 with rustup before running the script. This replay does not require
building the Lean project.

Success means exit status zero, `"status": "accepted"`, and:

```text
Checked 61851 declarations with no errors
```

The script requires all three target theorem names, rejects any axiom beyond
the three standard ones, and checks that the export stayed unchanged. Fresh
results are written to `logs/nanoda.log`, `logs/nanoda-result.json`, and
`logs/nanoda-theorem.txt`. Use a fresh extracted copy to preserve the original
logs. Use `PUBLIC-SHA256SUMS` for the public package: the older historical
inventory also lists three auxiliary files omitted to remove local paths.

### 3. Reproduce Comparator, Lean kernel replay, and both rejection tests

Use a fresh extraction of the same archive, with elan available as in step 1
and the Python/build prerequisites from step 2. Starting in the extracted
`theorem1-public-verification` directory:

```sh
cd lean-quantum
./run-lake.sh exe cache get
./check.sh
cd ../comparator-verification
./setup-tools.sh
./bootstrap-nanoda.sh
python3 run-checks.py
```

The setup script builds the exact pinned Comparator and exporter; there is no
need to find a compatible `lean4export` manually. `run-checks.py` performs:

1. Comparator comparison for the main theorem and both block-limit identities,
   permitted-axiom checking, and replay in Lean's kernel.
2. A changed-statement control, which must be rejected for a statement mismatch.
3. A missing-proof control, which must be rejected for using `sorryAx`.
4. A separate nanoda replay of the newly exported positive solution.

The script succeeds only if all expected outcomes occur, the positive Lean
kernel replay passes, and the proof sources stay unchanged. Success ends with
`Requested checks completed successfully.` The positive log,
`logs/comparator.log`, must include:

```text
Lean default kernel accepts the solution
Your solution is okay!
```

The negative controls should fail for their intended reasons; build failures
do not count as successful rejection tests. Their logs and JSON result records
are in `logs/negative-statement*` and `logs/negative-axiom*`.

After `setup-tools.sh`, to run **only Comparator** from the bundle's
`comparator-verification` directory:

```sh
./run-lake.sh env ../.tools/comparator/.lake/build/bin/comparator config.json
```

`enable_nanoda: false` in that configuration disables only Comparator's optional
nanoda integration. **Lean kernel replay still runs**; `run-checks.py` runs
nanoda separately. The archive's `Challenge` and `Solution` module names differ
from the repository's entry points, but their original mathematical sources
are identical, as recorded in [Verification/source-identity.json](Verification/source-identity.json).

These bundled scripts reproduce the recorded **unsandboxed development mode**.
For Linux sandbox isolation, follow the
[pinned Comparator instructions](https://github.com/leanprover/comparator/tree/066c3bc9e966ccad9a633d780ae4de13cd0f27b6),
including their trusted-reference and clean-environment requirements; simply
running the bundled scripts on Linux does not enable a sandbox. See
[ComparatorChallenges](ComparatorChallenges/README.md) for the repository's
own reference modules and configuration.

### What the certificate establishes

The recorded checks passed for `QuantumChannelContinuity.theorem_one`,
`QuantumChannelContinuity.blockRenyi_tendsto_regularized`, and
`QuantumChannelContinuity.blockRelative_tendsto_regularized`. Comparator
matched the statements and referenced definitions, checked the permitted
axioms, and replayed the solution in Lean's kernel. Nanoda independently
accepted the same export. [Verification](Verification/README.md) gives the
historical record and source hashes.

This is an unsigned local verification record. The reference was recorded
after proof development. These checks verify the recorded formal statements;
correspondence to the paper still requires mathematical review. Replaying the
retained export checks that export; the full reproduction additionally rebuilds
the proof from source and compares it against the separate reference.

## Attribution

This repository follows the presentation of
[openai/ten-proofs](https://github.com/openai/ten-proofs). Formalization metadata,
scope, and AI assistance are recorded in [formalization.yaml](formalization.yaml).
See [THIRD_PARTY.md](THIRD_PARTY.md) for dependency licenses and adapted proofs.
The code is released under [Apache-2.0](LICENSE).
