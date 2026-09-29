# Independent checking with Comparator

The [challenge](ChannelRenyiContinuity.lean) states the main continuity theorem
and the two block-limit identities separately from their proofs. It imports the
concrete definitions in `QuantumChannelContinuity.Regularization`, while the
[solution module](../ChannelRenyiContinuity.lean) imports the completed original
proof. The challenge's three `sorry` bodies are deliberate reference holes;
they are not part of the solution or the `All` build.

The [positive configuration](ChannelRenyiContinuity.json) asks
[Comparator](https://github.com/leanprover/comparator) to match all three theorem
statements and their referenced definitions, admit only `propext`,
`Quot.sound`, and `Classical.choice`, and replay the solution in Lean's kernel.
The [wrong-statement](WrongStatement.json) and
[missing-proof](MissingProof.json) configurations are rejection controls. They
should fail, respectively, with a statement mismatch and an illegal `sorryAx`.

## One-command reproduction

With elan, Git, native build tools, and Python 3.9+ installed, run from the
repository root:

```sh
./check-comparator.sh
```

This builds the pinned tools, runs the positive check and Lean kernel replay,
and requires both controls to fail for the expected reasons. It saves logs and
a machine-readable result in a fresh `.lake/comparator-check/` directory.
Success ends with `COMPARATOR CHECK PASSED`. The reproducer uses the upstream
development launcher without sandbox isolation; nanoda is a separate check.
See [VERIFYING.md](../VERIFYING.md) for setup and expected outputs.

## Manual configuration

The project pins Lean `v4.29.0-rc6`, Lean-Quantum
`bf1c4f6aaec84948f1a1c76c0728432813404a0f`, mathlib
`f156f7abd91ac67adb22bf999e5a71ba22e22e41`, and Comparator
`066c3bc9e966ccad9a633d780ae4de13cd0f27b6` in its toolchain and Lake
manifest. With [elan](https://github.com/leanprover/elan) installed, build the
proof and reference modules from the repository root:

```sh
lake exe cache get
lake build All ComparatorChallenges
```

Comparator also needs compatible `lean4export` and `landrun` executables on
`PATH`. Follow [the pinned Comparator setup](https://github.com/leanprover/comparator/tree/066c3bc9e966ccad9a633d780ae4de13cd0f27b6)
for Linux sandboxed checking. Once those tools are available, run:

```sh
lake exe comparator ComparatorChallenges/ChannelRenyiContinuity.json
```

For macOS reproduction, the [verification release archive](../Verification/README.md)
contains pinned setup scripts and the upstream development launcher used in the
recorded run. That launcher runs without sandbox isolation. The historical
Comparator run used `enable_nanoda: false`; it then checked the same retained
solution export with the independent nanoda kernel in a separate strict run.
The archive gives the exact export, checker pin, script, and recorded output.

The historical check passed all three positive targets and correctly rejected
both controls. The reference was recorded after proof development, so the
check establishes a match to this formal specification; correspondence to the
manuscript still calls for mathematical review. See the [verification
summary](../Verification/README.md) for the result and trust scope.
