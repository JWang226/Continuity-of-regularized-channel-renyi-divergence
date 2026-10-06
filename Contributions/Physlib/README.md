# Physlib candidate: trace-power derivative

This [patch](trace-power-derivative.patch) adds
`HermitianMat.hasDerivAt_trace_rpow`: for any positive semidefinite complex
Hermitian matrix and any positive exponent, the exponent derivative of its
power's trace is the trace of `x ^ s * log x` under functional calculus.
Singular matrices are included. The existing entropy proof at exponent one
then specializes this public result in three lines.

Prepared against Physlib commit
`d9a67555d722e4ff82438d9b67a635873145d9ac`, with Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Only two existing files change;
there are no new imports. The mathematical proof is adapted from this project's
`hasDerivAt_trace_rpow_nonneg` in
[StateSupportLimits.lean](../../QuantumChannelContinuity/StateSupportLimits.lean#L120).
Existing upstream copyright and license notices are preserved.

## Reviewer map and proposed PR description

The entropy implementation currently contains a private proof only at exponent
one. This change exposes a general positive-exponent trace derivative and
reuses it for that entropy calculation, including matrices with zero eigenvalues.

1. `QuantumInfo/ForMathlib/HermitianMat/Rpow.lean`: adds
   `HermitianMat.hasDerivAt_trace_rpow`. The spectral trace formula reduces the
   proof to scalar derivatives. A zero eigenvalue contributes zero on a
   neighborhood of every positive exponent. The module documentation is
   organized to the current repository convention.
2. `QuantumInfo/Entropy/Relative.lean`: replaces the body of the private
   `hasDerivAt_trace_rpow_at_one` with a specialization of the public lemma.
   Its statement and hypotheses are unchanged. No definition or existing lemma
   is removed.

Searches by derivative names and by spectral/trace/functional-calculus concepts
found the private order-one lemma and the necessary scalar API, but no public
equivalent in the inspected pinned sources. A separate agent reviewed the
mathematics and API. Detailed observed checks and their hashes are recorded in
[trace-power-derivative.json](trace-power-derivative.json).

## Apply and check

From this project's root, with elan and the native build tools installed:

```sh
patch_file="$PWD/Contributions/Physlib/trace-power-derivative.patch"
git clone https://github.com/leanprover-community/physlib.git physlib-trace-review
cd physlib-trace-review
git switch --detach d9a67555d722e4ff82438d9b67a635873145d9ac
git switch -c trace-power-derivative
git apply --check "$patch_file"
git apply "$patch_file"
export PATH="$HOME/.elan/bin:$PATH"
# On macOS, if Xcode is not configured:
# export DEVELOPER_DIR=/Library/Developer/CommandLineTools
lake exe get_cache
lake build Physlib QuantumInfo PhyslibAlpha
lake exe lint_all
lake exe runPhyslibLinters
lake exe forMathlib_lint
lake exe module_doc_lint
lake exe auxillary_script_test
git add QuantumInfo/ForMathlib/HermitianMat/Rpow.lean QuantumInfo/Entropy/Relative.lean
git commit -m "feat: differentiate the trace of positive matrix powers"
./scripts/lint/required/lint-style.sh
```

Read lint output: at this pinned revision `lint_all` returns zero even if a
child check fails. The record distinguishes required checks, optional lint
findings, and the changed module's direct documentation check without exemptions.
The patch was also applied to a separate temporary index at the exact base;
the resulting tree matched the prepared commit exactly.

## Human review before submission

No upstream pull request has been opened. Review the statement, both proof
changes, and the pinned repository policies before submission. Physlib's
[AI policy](https://github.com/leanprover-community/physlib/blob/d9a67555d722e4ff82438d9b67a635873145d9ac/AI-POLICY.md)
requires a human to “vouch that each definition, theorem statement, and proof
step means what it claims” and to confirm content/structure compliance before
opening the PR. It also requires humans to handle reviewer communication.

This work was assisted by Codex (OpenAI). The local preparation commit records
that assistance truthfully. The pinned `AGENTS.md` asks for a Claude-specific
coauthor trailer; that trailer is not used because Claude did not author this
contribution. The human submitter should resolve the appropriate attribution
convention when certifying compliance. No new bibliographic citations are added.
