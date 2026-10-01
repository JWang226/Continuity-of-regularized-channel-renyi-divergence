# Verify the proof and certificate

[Back to the README](README.md)

There are three useful checks. You can build the Lean source and audit its
axioms, independently check proof exports with Nanoda, or
reproduce the full Comparator check and its rejection tests. The commands below
use a macOS or Linux terminal and do not require the author's local files.

## Comparator reproducer for this checkout

With elan, Git, native build tools, and Python 3.9+ installed, run from the
repository root:

```sh
./check-comparator.sh
```

The script downloads dependency caches, builds the pinned Comparator and
exporter, verifies their source revisions, and checks the three theorem targets
with Lean kernel replay. It then requires the wrong-statement and missing-proof
controls to fail for their intended reasons. Build failures are not accepted
as successful rejection tests. Proof sources and configurations must remain
unchanged during the run.

Success ends with:

```text
COMPARATOR CHECK PASSED: three theorem targets, Lean kernel replay, and both rejection controls.
```

Every run gets a new directory under `.lake/comparator-check/`, containing
`positive.log`, the two rejection logs, source hashes, and `result.json` with
exit statuses and a final `PASS` or `FAIL`. Use `./check-comparator.sh --skip-cache`
when dependency caches are already prepared. The script does not install elan;
follow the setup below if `lake` is missing.

This reproducer uses the pinned upstream **unsandboxed development launcher**
on both macOS and Linux. It runs Comparator's Lean kernel replay; the separate
nanoda replay and historical release-certificate reproduction are described
below. It does not regenerate or overwrite the released certificate.

## Nanoda reproducer for this checkout

With the same elan, Git, native build tools, and Python 3.9+ prerequisites, run:

```sh
./check-nanoda.sh
```

This builds the current Lean proof and pinned exporter, builds Nanoda at
`3a2407216ee84a75f9e1aead6803d0578be06ae7`, and runs the checker's own tests.
It exports the three theorem targets and their dependencies, then checks that
fresh export with Nanoda's independent kernel. All three target names must
exist, and only `propext`, `Quot.sound`, and `Classical.choice` are permitted.
Any other axiom is a hard error. The source and export must remain unchanged.

An existing Rust/Cargo installation is reused. If Cargo is unavailable, the
bootstrap installs Rust 1.98.1 inside `.lake/nanoda-tools`, without changing
shell profiles. curl is needed for that installation. If an existing compiler
is too old, select Rust 1.98.1 with rustup before running the script.

Success ends with `NANODA CHECK PASSED`. A fresh directory under
`.lake/nanoda-check/` retains `Solution.ndjson`, `nanoda.log`, `theorems.txt`,
source/export hashes, the strict checker configuration, and `result.json`.
The uncompressed export needs about 500 MB of disk space. Use
`./check-nanoda.sh --skip-cache` when dependencies are already prepared.

This checks a fresh export from the current checkout. It complements
Comparator's statement comparison; Nanoda alone checks proof terms and the
configured axiom restrictions. To replay the exact historical export from the
released certificate instead, follow step 2 below.

## 1. Build the Lean proof and audit its axioms

Install Git and native build tools (Xcode Command Line Tools on macOS, or C/C++
build tools on Linux). If Lean is not installed, install
[elan](https://github.com/leanprover/elan#installation), its toolchain manager:

```sh
curl -fsSL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none --no-modify-path
export PATH="$HOME/.elan/bin:$PATH"
```

This installs the `lake` launcher in `~/.elan/bin` without changing shell
profiles. The project wrapper finds it there automatically; the `PATH` export
also makes it available to the certificate bundle's setup scripts in this
terminal. The exact Lean version is selected by the project's `lean-toolchain`
file and downloaded on first use. You do not need to choose a default version.

For a new checkout, run:

```sh
git clone https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence.git
cd continuity-of-regularized-channel-renyi-divergence
./run-lake.sh --version
./run-lake.sh exe cache get
./check.sh
```

If you already cloned the repository, run these last three commands inside
your existing checkout after installing elan. If you see `lake: not found`,
complete the installation above first. For a custom installation, set
`ELAN_HOME` to the directory containing elan's `bin` and `toolchains` folders.
The version check should identify Lake built for Lean `4.29.0-rc6`.

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

## 2. Download and independently check the proof certificate

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

## 3. Reproduce Comparator, Lean kernel replay, and both rejection tests

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
from the repository's entry points. Their original mathematical sources match
the historical public checkout recorded in [Verification/source-identity.json](Verification/source-identity.json).
The current checkout adds only copyright/license headers to those proof files,
as checked by [Verification/current-source-identity.json](Verification/current-source-identity.json).

These bundled scripts reproduce the recorded **unsandboxed development mode**.
For Linux sandbox isolation, follow the
[pinned Comparator instructions](https://github.com/leanprover/comparator/tree/066c3bc9e966ccad9a633d780ae4de13cd0f27b6),
including their trusted-reference and clean-environment requirements; simply
running the bundled scripts on Linux does not enable a sandbox. See
[ComparatorChallenges](ComparatorChallenges/README.md) for the repository's
own reference modules and configuration.

## What the certificate establishes

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
