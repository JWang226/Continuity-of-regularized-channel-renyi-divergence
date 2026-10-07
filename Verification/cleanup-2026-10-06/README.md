# Fresh cleanup verification

This unsigned local record binds the completed cleanup checks to the current source identity and proof index. It retains the all-declaration Lean axiom audit, Comparator comparison and Lean kernel replay, both intended rejection controls, Nanoda independent replay, and current statement/definition probes with live dependency hashes.

See [summary.json](summary.json) for exact counts, hashes and scope. Original local log hashes and sanitized publication hashes are separate. The full Nanoda export is hashed but not included here; regenerate and independently check it with the public reproducer. This does not rewrite the historical certificate or repeat the dated informal assessment. No signature or human review is claimed.

Reproduce from the repository root with `./check.sh`, `./check-comparator.sh --skip-cache`, `./check-nanoda.sh --skip-cache`, and `python3 scripts/check-statement-audit.py`. See [VERIFYING.md](../../VERIFYING.md) for setup and interpretation.

The public scripts are the principal reproducers. For direct replay of the published portable configuration, regenerate an export with the same pinned source, copy the fresh `Solution.ndjson` into this record directory, and verify its SHA-256 matches `summary.json` before running the pinned checker from this directory:

```sh
../../.lake/nanoda-tools/nanoda_lib/target/release/nanoda_bin nanoda-config.json
```

The published configuration changes only `export_file_path` and `pp_output_path` from the checked original. All checking policy remains unchanged. Replay writes `replayed-theorems.txt`, preserving the retained `nanoda-theorems.txt`. Original and published configuration hashes and the exact two-field transformation are recorded in `summary.json`.
