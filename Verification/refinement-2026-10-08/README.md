# Review refinement verification — October 8, 2026

This unsigned record contains completed local checks of the documentation and
Comparator-test refinements from baseline commit
`e29274a69978bb499f00497481c6008befb0b84d`. The date uses the author's Pacific
time zone; checker timestamps use UTC. The completed proof library changed only
in a docstring. Its theorem statements and proof bodies are unchanged.

| Check | Result |
| --- | --- |
| Lean build and transitive axiom audit | PASS: 1,318 project declarations, including 1,090 theorems; only `propext`, `Quot.sound`, and `Classical.choice`. |
| Comparator positive comparison and Lean kernel replay | PASS for the three theorem targets and their exported dependency closure. |
| Wrong-statement control | Rejected for a statement mismatch. |
| Missing-proof control | Rejected for `sorryAx`. |
| One-sided-limit control | Rejected for a `theorem_one` statement mismatch after changing only the reference filter from `𝓝[≠] 1` to `𝓝[>] 1`. |
| Current statement/definition probes | PASS, with unchanged project and dependency inputs during the run. |
| Index regeneration | 1,268 declarations; names, kinds, elaborated types, and dependency/user lists match the baseline. |
| Artifact consistency | PASS. Historical assessments and verification records remain unchanged. |

[summary.json](summary.json) records the checks and hashes of retained files.
[comparator-result.json](comparator-result.json) and
[comparator-sources.json](comparator-sources.json) retain the runner's results
and 97 source/configuration/runner hashes. Logs are retained alongside them.
The Comparator run used the upstream unsandboxed development launcher.

Reproduce the fresh checks from the repository root with the pinned toolchain
and dependencies described in [VERIFYING.md](../../VERIFYING.md):

```sh
./check.sh
./check-comparator.sh --skip-cache
python3 scripts/check-statement-audit.py
python3 scripts/check-artifacts.py
```

Omit `--skip-cache` if dependency caches are not prepared. Index regeneration is
documented in the [proof map](../../docs/PROOF_MAP.md).

Nanoda was not rerun for this refinement. Its successful independent replay is
retained in the [October 6 cleanup record](../cleanup-2026-10-06/README.md);
`./check-nanoda.sh` produces a fresh check of the current checkout.

Matching hashes establish consistency with the recorded inputs, not
authentication of an unsigned execution. Comparator checks agreement with a
formal reference recorded after proof development. It does not establish that
the reference matches the informal paper; independent human correspondence
review remains outstanding. The frozen Prove2me contribution is separate and
unchanged.
