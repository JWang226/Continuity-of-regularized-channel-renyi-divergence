# Source identity rejection control

The full statement-audit checker was invoked with one deliberately incorrect current-source hash. It exited nonzero and wrote a failure result for the expected source path before compiling Lean. The exact original identity was restored in a `finally` block; the recorded original and restored hashes match.

[result.json](result.json) records the executed command, timestamps, altered hash, rejection and restoration. [failure-result.json](failure-result.json) and [console.log](console.log) preserve the actual rejection. [helper.txt](helper.txt) contains the exact local control driver, bound by its hash; [manifest.json](manifest.json) binds these evidence files. It is a driver listing rather than an installed public checker.

A subsequent complete positive statement-audit run replaces the temporary failure result under `.lake/statement-audit/`. The fresh cleanup verification record retains that final positive result. This control verifies rejection of a stale or altered source inventory; it does not establish correspondence between the English paper and Lean.
