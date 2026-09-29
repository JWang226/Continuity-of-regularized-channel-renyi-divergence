# Verification record

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
Lean source files to their unchanged historical SHA-256 hashes. The original
audit checked 1,327 project declarations, including 1,101 theorems. The proof
uses only `propext`, `Classical.choice`, and `Quot.sound`.

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
