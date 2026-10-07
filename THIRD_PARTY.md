# Formalization dependencies and attribution

The build pins Lean-Quantum at
[`bf1c4f6aaec84948f1a1c76c0728432813404a0f`](https://github.com/Hayata-Yamasaki-Group/lean-quantum/tree/bf1c4f6aaec84948f1a1c76c0728432813404a0f).
Its actual finite-dimensional operators, CPTP maps, support-aware divergences,
data-processing proofs, and faithful quasi-entropy derivative are reused.
These are imported Lean proofs, not paper references accepted as axioms.
Lean-Quantum is Apache-2.0 licensed; its license remains in the dependency.

`QuantumChannelContinuity/StateOrderApprox.lean` adapts the spectral
faithful-approximation continuity proofs from
[`SandwichedRenyiNonNeg.lean` at the pinned Lean-Quantum revision](https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean).
Those declarations are private upstream, so the adapted proofs are checked
as part of this project. The original copyright notice is retained; the
Apache-2.0 license text is included in `LICENSE-MATHLIB`.

The transitive mathlib revision is
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`.
All dependency revisions are recorded in `lake-manifest.json`.

The [pre-cleanup source snapshot](Verification/source-snapshots/pre-cleanup-2026-10-06.json)
also retains five unmodified Lean-Quantum and eleven unmodified mathlib source
files used as inputs to the dated audits, at the revisions listed above. Their
original copyright, author and Apache-2.0 notices are preserved. The included
`LICENSE-MATHLIB` supplies the Apache-2.0 license text for these archived copies.

`QuantumChannelContinuity/Minimax.lean` adapts
[`Mathlib/Topology/Sion.lean` at `2be1d7728238e3c007b68094fa0abc562f8077df`](https://github.com/leanprover-community/mathlib4/blob/2be1d7728238e3c007b68094fa0abc562f8077df/Mathlib/Topology/Sion.lean).
The original copyright and author notice is retained. The adaptation supplies
four compatibility declarations for the pinned mathlib version and removes
the newer module visibility directives. The complete adapted minimax proof is
checked locally. It remains available as preparatory infrastructure; the
exact `HockeySlackAttainment` theorem is proved separately using separation
of a closed semidefinite cone and a concrete Choi tester representation in
`SDPCone.lean` through `SlackAttainment.lean`. The Apache-2.0 license is
reproduced in `LICENSE-MATHLIB`.

QICLean was inspected as a possible source of ordered dilation factorization.
No QICLean source is copied into this project. The implemented factorization
uses a proved finite-dimensional Douglas contraction argument instead.

`scripts/comparator-development-landrun.sh` is copied unchanged from
[`scripts/fake-landrun.sh` in Comparator at `fd5d5bcf14177b187f66d4502071268d877887c3`](https://github.com/leanprover/comparator/blob/fd5d5bcf14177b187f66d4502071268d877887c3/scripts/fake-landrun.sh).
It is Apache-2.0 licensed, covered by the included `LICENSE`, and deliberately
provides no sandbox isolation. The reproducer verifies its SHA-256 before use.

The Nanoda reproducer builds
[`nanoda_lib` at `3a2407216ee84a75f9e1aead6803d0578be06ae7`](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7)
from unmodified upstream source. Nanoda is Apache-2.0 licensed; its source and
license are retained in the local tool checkout under `.lake/nanoda-tools`.
