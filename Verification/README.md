# Verification record

The [fresh cleanup record](cleanup-2026-10-06/README.md), assembled on
7 October 2026 UTC, checks the cleaned source separately. The Lean audit passed
for **1,318 project declarations and 1,090 theorems**; Comparator accepted all
three targets, replayed them through Lean's kernel, and rejected both negative
controls. Nanoda checked **61,840 declarations with no errors**. Current
statement probes also passed. [Its summary](cleanup-2026-10-06/summary.json)
binds the source identity, proof index, strict checking policy and logs. This
unsigned record preserves the historical certificate and assessments below;
it does not claim a new informal assessment or independent human review.

The formalization has an unsigned local verification record from 29 September
2026. [Comparator](https://github.com/leanprover/comparator) accepted the
[main theorem](../QuantumChannelContinuity/Main.lean) and both
[block-limit identities](../QuantumChannelContinuity/RegularizationLimits.lean)
against a separate reference challenge. A second kernel, nanoda 0.4.19,
checked the identical solution export: **61,851 declarations, no errors**.
Two negative controls were rejected for the expected reasons: a changed
statement and an unproved statement using `sorryAx`.

[summary.json](summary.json) gives the public machine-readable result,
[historical-nanoda-theorem.txt](historical-nanoda-theorem.txt) shows the
independent checker's rendering of the three target statements and admitted
axioms. The [recorded checker output](historical-nanoda-output.txt) reports
successful replay. [source-identity.json](source-identity.json) maps 82 mathematical
Lean source files to their unchanged historical SHA-256 hashes at public commit
`70f9371910f418c02f96f561510daa4260c733ae`. The original
audit checked 1,327 project declarations, including 1,101 theorems. The proof
uses only `propext`, `Classical.choice`, and `Quot.sound`.

The pre-cleanup checkout added copyright/license comment headers to 80 of those
82 files; the two existing upstream notices were preserved. Its exact audited
inputs are retained in the [source snapshot](source-snapshots/pre-cleanup-2026-10-06.json)
at commit `c1042369444d325216ef75e2c7cf866580e2035b`. The snapshot preserves the
header-only relationship to the historical source and the bytes used by the
dated agent assessments.

Later code cleanup is recorded separately by the
[current source identity](current-source-identity.json), including modified,
added and removed source paths. It does **not** assign the historical certificate
or assessments to new proof bytes. The historical certificate, hashes, release
assets and assessment JSON files have not been rewritten. Run
`python3 scripts/check-artifacts.py` to validate the retained snapshot and
current metadata, and the [verification commands](../VERIFYING.md) to check the
current proof. Source identity is bookkeeping, not a proof certificate.

[Lean read-back](../docs/LEAN_READBACK.md) was produced by a separate agent that
did not consult the manuscript. A [subsequent paper comparison](../docs/PAPER_COMPARISON.md)
records its correspondence and scope. Both are AI-assisted review artifacts;
independent human mathematical review remains outstanding. Their input hashes
are validated against the retained snapshot. The statement-audit reproducer
compiles fresh mechanical probes against the current source; it does not rerun
the historical informal interpretation or supply a new human assessment.

The full replayable record is distributed as a
[GitHub release asset](https://github.com/JWang226/continuity-of-regularized-channel-renyi-divergence/releases/tag/v1.0.0),
`theorem1-public-verification.zip`, with a matching `.sha256` file. It includes
the **unchanged historical `certificate.json`**, the complete compressed
challenge and solution exports, reference modules, logs, scripts, and the
original proof source. The certificate's SHA-256 is
`82e88be8e0450ced78fe482a9495b97533c2a60a548743ccf300786ef721e5ed`.
The uncompressed solution export is 495,343,344 bytes with SHA-256
`57fb97982ebd07c707f47484966d87cbfd1b1a39af19eee3e21d082649f5c5bc`.
The package contains its own public file-hash inventory and instructions.

The public archive omits three original auxiliary files that recorded an
absolute local machine path: `nanoda-config.json`,
`logs/nanoda-bootstrap.log`, and `nanoda-tests.log`. The replay scripts
regenerate the necessary configuration. The original historical certificate
and proof exports remain byte-for-byte unchanged; the public summary and
package inventory are newly derived and do not purport to be part of the
original record. No third-party signature is claimed.

The check used Comparator's upstream **unsandboxed macOS development launcher**.
It establishes statement and definition matching, permitted axioms, and two
kernel replays for the recorded formal targets. It does not establish Linux
sandbox isolation or, by itself, that the Lean definitions express every
aspect of the English manuscript. The separate reference was recorded after
proof development. These boundaries are described in the archive's report and
review notes.
