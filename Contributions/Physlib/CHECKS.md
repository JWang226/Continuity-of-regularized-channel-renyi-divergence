# Observed Physlib candidate checks

These are sanitized excerpts from local runs, not a signed certificate. Full raw-log hashes are recorded in `trace-power-derivative.json`. Repository declaration linters retain their existing exemptions; the changed module documentation was also checked directly without an exemption.

## build

Command: `lake build Physlib QuantumInfo PhyslibAlpha`

Observed exit code: 0. Status: passed.

```text
✔ [5522/5551] Built QuantumInfo.ForMathlib.HermitianMat.Rpow (16s)
Build completed successfully (5551 jobs).
```

## api

Command: `lake env lean --stdin (exact API example, #check, #print axioms)`

Observed exit code: 0. Status: passed.

```text
@HermitianMat.hasDerivAt_trace_rpow : ∀ {d : Type u_1} [inst : Fintype d] [inst_1 : DecidableEq d]
  {A : HermitianMat d ℂ},
  0 ≤ A → ∀ {s : ℝ}, 0 < s → HasDerivAt (fun t => (A ^ t).trace) (A.cfc fun x => x ^ s * Real.log x).trace s
'HermitianMat.hasDerivAt_trace_rpow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## committed_style

Command: `./scripts/lint/required/lint-style.sh (after local commit)`

Observed exit code: 0. Status: passed.

```text
+ touch scripts/lint/exemptions/style-exceptions.txt
+ touch scripts/lint/exemptions/LinterExemption.txt
+ git ls-files 'Physlib/*.lean' 'QuantumInfo/*.lean'
+ grep -vxF -f scripts/lint/exemptions/LinterExemption.txt
+ xargs ./scripts/lint/required/lint-style.py
++ find . -name '*.lean' -type f '(' -perm -u=x -o -perm -g=x -o -perm -o=x ')'
+ executable_files=
+ [[ -n '' ]]
++ git ls-files
++ sort --ignore-case
++ uniq -D --ignore-case
+ ignore_case_clashes=
+ '[' -n '' ']'
```

## forMathlib

Command: `lake exe forMathlib_lint`

Observed exit code: 0. Status: passed.

```text
All 17 files in `Physlib.Mathematics.ForMathlib` import only from `Physlib.Mathematics.ForMathlib` and are used outside of it.
```

## module_docs

Command: `lake exe module_doc_lint`

Observed exit code: 0. Status: passed.

```text
✔ [177/214] Built Batteries.Logic:c.o (1.2s)
✔ [178/214] Built Mathlib.Basic.Nonempty:c.o (1.1s)
✔ [179/214] Built Mathlib.Basic.Nontrivial.Defs:c.o (1.2s)
✔ [180/214] Built Mathlib.Basic.ExistsUnique:c.o (1.9s)
✔ [181/214] Built Mathlib.Data.String.Defs:c.o (884ms)
✔ [182/214] Built Batteries.Util.ExtendedBinder:c.o (2.1s)
✔ [183/214] Built Mathlib.Tactic.Attr.Register:c.o (3.5s)
✔ [184/214] Built Mathlib.Basic.Logic.Basic:c.o (4.1s)
✔ [185/214] Built Mathlib.Lean.PrettyPrinter.Delaborator:c.o (3.9s)
✔ [186/214] Built Mathlib.Lean.Meta.Simp:c.o (5.4s)
✔ [187/214] Built Mathlib.Tactic.Eqns:c.o (592ms)
✔ [188/214] Built Mathlib.Tactic.Translate.Attributes:c.o (356ms)
✔ [189/214] Built Mathlib.Tactic.Push.Attr:c.o (5.7s)
✔ [190/214] Built Batteries.Lean.NameMapAttribute:c.o (2.3s)
✔ [191/214] Built Mathlib.Tactic.Translate.GuessName:c.o (3.0s)
✔ [192/214] Built Mathlib.Tactic.Translate.ToDual:c.o (2.8s)
✔ [193/214] Built Mathlib.Tactic.ToDual:c.o (466ms)
✔ [194/214] Built Mathlib.Tactic.SetNotationForOrder:c.o (6.5s)
✔ [195/214] Built Mathlib.Tactic.Translate.TagUnfoldBoundary:c.o (4.5s)
✔ [197/214] Built Mathlib.Logic.Function.Defs:c.o (771ms)
✔ [198/214] Built Mathlib.Order.Defs.Unbundled:c.o (445ms)
✔ [199/214] Built Mathlib.Logic.Function.Basic:c.o (804ms)
✔ [200/214] Built Mathlib.Data.Set.Defs:c.o (2.6s)
✔ [201/214] Built Mathlib.Tactic.ExtendDoc:c.o (1.5s)
✔ [207/214] Built Mathlib.Util.AddRelatedDecl:c.o (11s)
✔ [208/214] Built Mathlib.Tactic.Translate.Reorder:c.o (9.6s)
✔ [209/214] Built Mathlib.Tactic.Translate.UnfoldBoundary:c.o (10s)
✔ [210/214] Built Batteries.Tactic.Trans:c.o (13s)
✔ [211/214] Built module_doc_lint (19s)
✔ [212/214] Built module_doc_lint:c.o (4.3s)
✔ [213/214] Built Mathlib.Tactic.Translate.Core:c.o (36s)
✔ [214/214] Built module_doc_lint:exe (4.8s)
No documentation style issues found.
```

## changed_module_docs

Command: `lake env lean --stdin (checkHeadings on changed Rpow without exemptions)`

Observed exit code: 0. Status: passed.

```text
Changed Rpow module documentation passed without exemptions.
```

## auxiliary_scripts

Command: `lake exe auxillary_script_test`

Observed exit code: 0. Status: passed.

```text
(1/4) lake exe make_tag
Passed.
(2/4) lake exe TODO_to_yml mkFile
Passed.
(3/4) lake exe stats mkHTML
Passed.
(4/4) lake exe informal mkFile mkDot mkHTML
Passed.
All auxiliary scripts passed.
```

## file_imports

Command: `lake exe check_file_imports`

Observed exit code: 0. Status: passed.

```text
All files are imported correctly into Physlib.lean.
All files are imported correctly into QuantumInfo.lean.
```

## alpha_imports

Command: `lake exe noAlphaImports`

Observed exit code: 0. Status: passed.

```text
No violations found. All files passed the check.
```

## alpha_root_imports

Command: `lake exe alphaFileImports`

Observed exit code: 0. Status: passed.

```text
✓ All 304 .lean files in ./PhyslibAlpha are imported in ./PhyslibAlpha.lean
```

## duplicate_tags

Command: `lake exe check_dup_tags`

Observed exit code: 0. Status: passed.

```text
Checking for duplicate tags.
Linter finished, no duplicaate tags found.
```

## sorry_attributes

Command: `lake exe sorry_lint`

Observed exit code: 0. Status: passed.

```text
Checking sorryful results.
Sorryful/pseudo results are all correctly attributed test passed.
```

## declaration_linters

Command: `lake exe runPhyslibLinters`

Observed exit code: 0. Status: passed-with-existing-exemptions.

```text
Results been linted with the following linters:
#[checkType, defsWithUnderscore, deprecatedNoSince, docBlame, impossibleInstance, nonClassInstance, simpComm, simpNF, structureInType, subsetDotNotationLinter, synTaut, tacticAlt, tacticDocs, unusedArguments, unusedHavesSuffices]
Starting parallel running on linters on all declarations. Results if any are
      shown below.
-- Linting passed for Physlib.
Results been linted with the following linters:
#[checkType, defsWithUnderscore, deprecatedNoSince, docBlame, impossibleInstance, nonClassInstance, simpComm, simpNF, structureInType, subsetDotNotationLinter, synTaut, tacticAlt, tacticDocs, unusedArguments, unusedHavesSuffices]
Starting parallel running on linters on all declarations. Results if any are
      shown below.
-- Linting passed for QuantumInfo.
```

## lint_all

Command: `lake exe lint_all`

Observed exit code: 0. Status: completed-with-optional-import-findings.

```text
(1/7) Style lint
This linter is not checked by GitHub but if you have time please fix these errors.

(2/7) Building
Build is successful.

(3/7) File imports
All files are imported correctly into Physlib.lean.
All files are imported correctly into QuantumInfo.lean.

(3/7) Illegal Imports
No violations found. All files passed the check.

(3/7) Ensuring all PhyslibAlpha modules imported
✓ All 304 .lean files in ./PhyslibAlpha are imported in ./PhyslibAlpha.lean

(3/7) ForMathlib imports and uses
All 17 files in `Physlib.Mathematics.ForMathlib` import only from `Physlib.Mathematics.ForMathlib` and are used outside of it.

(4/7) TODO tag duplicates
Checking for duplicate tags.
Linter finished, no duplicaate tags found.

(5/7) Sorry and pseudo attribute linter
Checking sorryful results.
Sorryful/pseudo results are all correctly attributed test passed.


(6/7) Lean linter
Expect this linter to take a while to run, it can be skipped with
      lake exe lint_all --fast
You can manually perform this linter by placing `#lint` at the end of the files you have modified.
Results been linted with the following linters:
#[checkType, defsWithUnderscore, deprecatedNoSince, docBlame, impossibleInstance, nonClassInstance, simpComm, simpNF, structureInType, subsetDotNotationLinter, synTaut, tacticAlt, tacticDocs, unusedArguments, unusedHavesSuffices]
Starting parallel running on linters on all declarations. Results if any are
      shown below.
-- Linting passed for Physlib.

(7/7) Transitive imports
Expect this linter to take a while to run, it can be skipped with
        lake exe lint_all --fast


Error: Transitive imports in Physlib/ClassicalMechanics/FreeParticle/Basic.lean (please remove them):
[Mathlib.Analysis.Calculus.MeanValue]


```

## Optional redundant import findings

The wrapper reported redundant imports in 18 unchanged files. The patch adds no imports, and no edited file was reported. Each listed file was checked byte-for-byte against the base.

- `Physlib/ClassicalMechanics/FreeParticle/Basic.lean`
- `Physlib/Cosmology/FLRW/Basic.lean`
- `Physlib/Cosmology/FLRW/MatterContent.lean`
- `Physlib/Cosmology/FLRW/Solutions.lean`
- `Physlib/Mathematics/Calculus/Divergence.lean`
- `Physlib/Mathematics/Distribution/PowMul.lean`
- `Physlib/Mathematics/ForMathlib/List.lean`
- `Physlib/Mathematics/Groups/SpecialUnitary/LieAlgebra/Basic.lean`
- `Physlib/Mathematics/InnerProductSpace/Gaussian.lean`
- `Physlib/QFT/PerturbationTheory/FieldSpecification/NormalOrder.lean`
- `Physlib/QFT/PerturbationTheory/FieldSpecification/TimeOrder.lean`
- `Physlib/QFT/PerturbationTheory/Koszul/KoszulSign.lean`
- `Physlib/QFT/PerturbationTheory/Koszul/KoszulSignInsert.lean`
- `Physlib/QFT/PerturbationTheory/WickContraction/ExtractEquiv.lean`
- `Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean`
- `Physlib/QuantumMechanics/HilbertSpaces/SpaceD/Basic.lean`
- `Physlib/QuantumMechanics/Operators/OneDimension/Parity.lean`
- `Physlib/SpaceAndTime/Time/Derivatives.lean`
