# Statement and definition audit

The three Comparator targets match the paper for **nonzero finite-dimensional
complex Hilbert spaces**, with Rényi orders at least one half and different
from one. No support, finiteness, Stinespring, filter, Schatten, or other
proof-step hypotheses occur in their types. Infinite divergence is included.

This audit also adds a Lean proof that the paper's `id ⊗ N` convention and the
implementation's `N ⊗ id` convention give the same optimized divergences.
Two qualifications remain explicit: the paper does not spell out the nonzero
space convention, and Lean's total functions assign values outside the paper's
order domain. This is an agent review with mechanical checks, not independent
human certification of the paper-to-Lean correspondence.

## Source and method

Audited on 2026-10-06 against [arXiv:2609.28635v1](https://arxiv.org/html/2609.28635v1),
Theorem 1 and Section 1.1, Equations (1.1)–(1.5). The retained
[development manuscript](source-manuscript.tex) corroborates these statements;
it is not asserted to be byte-identical to the arXiv source archive.

The original proof checkout was `240d8acc8c6c23ec4952a63e11b9e8b65979ab9e`.
The [machine-readable report](statement-audit.json) pins exact declaration
ranges, elaborated types, complete input-file hashes, source locators, binder
classifications, definition findings, and reproducible checks. It records the
rendered HTML capture separately from the retained manuscript.

Two fresh agents reconstructed the source before inspecting the Lean
statements and definitions. They did not open the earlier read-back or
comparison reports before forming their findings. They inherited task context,
so this was not a blind, isolated review. A separate agent reviewed
the newly written tensor-swap bridge. These are independent agent checks;
none records human approval.

The workflow applies
[lean-statement-audit](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/70bb859295edc2abb9ad81f8f6e31ab2adf8ca07/skills/lean-statement-audit/SKILL.md)
to an existing completed proof. It does not invent a historical frozen-draft
approval process. Definition correspondence is assessed on the paper's domain.
The skill's unmodified global-carrier rule would flag totalized off-domain
values; **a literal, unmodified skill pass is not claimed**.

## Exact statements and binders

| Target | Paper locator | Solution |
| --- | --- | --- |
| `QuantumChannelContinuity.theorem_one` | Theorem 1, Eq. (1.1) | [Main.lean](../QuantumChannelContinuity/Main.lean#L49) |
| `QuantumChannelContinuity.blockRenyi_tendsto_regularized` | Rényi instance of Eq. (1.5) | [RegularizationLimits.lean](../QuantumChannelContinuity/RegularizationLimits.lean#L118) |
| `QuantumChannelContinuity.blockRelative_tendsto_regularized` | Relative-entropy instance of Eq. (1.5) | [RegularizationLimits.lean](../QuantumChannelContinuity/RegularizationLimits.lean#L127) |

The [challenge](../ComparatorChallenges/ChannelRenyiContinuity.lean) declares
these same propositions separately. Its deliberate specification holes are not
solution proofs. The block identities establish the limit interpretation of
the supremum definitions used in the main theorem; they are two instances of
one regularization identity, rather than extra numbered main theorems.

The common surface binders below apply to all three targets; `A, B` replace
`H, K` in the block identities.

| Binder | Form and type | Bin | Source basis |
| --- | --- | --- | --- |
| `H` | implicit `Type` (universe zero) | TYPING | Input-space carrier, §1.1 |
| `K` | implicit `Type` (universe zero) | TYPING | Output-space carrier, §1.1 |
| `Qudit H` | instance | STANDING | Finite complex Hilbert space, §1.1 |
| `Qudit K` | instance | STANDING | Same |
| `Nontrivial H` | instance | STANDING, under the stated convention | Nonzero quantum system; implicit in paper |
| `Nontrivial K` | instance | STANDING, under the stated convention | Same |
| `N` | explicit `CPTP H K` | SOURCE | First supplied channel |
| `M` | explicit `CPTP H K` | SOURCE | Second supplied channel |

The Rényi block identity inserts these before `N, M`:

| Binder | Form and type | Bin | Source basis |
| --- | --- | --- | --- |
| `p` | implicit `ℝ` | SOURCE | Rényi order, Eq. (1.3) |
| `hp` | explicit `1 / 2 ≤ p` | SOURCE | Admissible domain, Eq. (1.3) |
| `hp1` | explicit `p ≠ 1` | SOURCE | Excluded order, Eq. (1.3) |

| Target | SOURCE | STANDING | TYPING | RULED | EXCESS |
| --- | ---: | ---: | ---: | ---: | ---: |
| Main theorem | 2 | 4 | 2 | 0 | 0 |
| Rényi block identity | 5 | 4 | 2 | 0 | 0 |
| Relative block identity | 2 | 4 | 2 | 0 | 0 |

`Qudit` expands to 45 inherited fields describing the normed additive group,
complex inner product, completeness, and finite dimension. Each channel
expands to its function, additivity, complex scalar linearity, positivity of
every finite matrix amplification, and trace preservation. The expanded table
below and the JSON retain every field; no quantum estimate is bundled in these
interfaces. Expanded counts replace the interfaces with their fields, rather
than adding them to the surface counts: main/relative are SOURCE 10, STANDING
92, TYPING 2; Rényi is SOURCE 13, STANDING 92, TYPING 2. RULED and EXCESS are zero
under the documented nonzero-system interpretation.

## Definition findings

The JSON records `BODY_MATCH`, `PUBLIC_CARRIER`, `WELL_DEFINEDNESS`,
`CHARACTERIZATION`, `CHOICE_INDEPENDENCE`, and `DEFINITION_VERDICT` for each
source-facing object. These are literal constructions, so uniqueness-based
choice obligations are not applicable. The library's functional calculus is
used through its proved API; no project definition chooses an unconstrained
family to stand in for a source object.

| Objects | Checked meaning |
| --- | --- |
| `DensityState`, `PureInput.density` | Actual positive trace-one operators and rank-one states of every unit vector; singular states are included. |
| `stateRenyi`, `stateRelative`, `toBits` | Actual support-aware trace formulas, converted to base-two units; support mismatch and below-one zero overlap retain infinity. |
| Channel divergences | Supremum over all pure entangled inputs, with a reference copy of the full input space. |
| `EReal.toENNReal` conversion | Faithful on these nonnegative normalized-state divergences, proved and checked by exact re-embedding probes. |
| Tensor powers | Repeated supplied channels, ending at the one-dimensional tensor unit; existing one-copy and regrouping identities are proved. |
| Regularization | Supremum of normalized positive blocks; both separate limit identities are proved, including infinite limits. |

The value assigned at order one is zero. The main theorem uses `𝓝[≠] 1`,
which excludes that point and eventually lies above one half. A compiled
domain probe checks this. The block sequence's value at zero is also
irrelevant: regularization excludes zero blocks, and `atTop` ignores every
finite prefix. No claim of continuity at the assigned value at one is made.

For zero-dimensional algebraic spaces, the source's unit-vector optimization
would itself need an extra convention. This formalization does not cover that
degeneracy. The usual tensor-power dimension formula follows from the audited
recursion and standard dimension multiplication; an optional separate
`finrank` probe timed out and is not counted as checked evidence.

## Explicit tensor-factor correspondence

[SourceCorrespondence.lean](../QuantumChannelContinuity/SourceCorrespondence.lean)
defines `referenceFirstOutput` as the actual `id ⊗ N` channel action. It proves
the operator identity for every input operator, transports arbitrary density
states, and constructs a bijection of the complete unit-vector input domains.
It then proves:

- `referenceFirstOutput_swap`: swapping input and output factors intertwines
  the two actual channel actions, including entangled inputs.
- `channelRenyi_eq_referenceFirst`: the full optimized Rényi divergences agree
  at every admissible order.
- `channelRelative_eq_referenceFirst`: the full optimized relative entropies
  agree, including infinity.

The equality proofs consume the swap identity, the input bijection, and the
existing support-aware isometric invariance theorems. They do not assume an
optimization equality or restrict inputs to product states. This closes the
factor-order identification described mathematically in the earlier
[paper comparison](PAPER_COMPARISON.md).

The historical 82 proof files are unchanged. This supplementary module is
checked separately in Lean; the original Comparator/Nanoda certificate does
not include it.

## Reproduce the checks

After the [normal dependency setup](../README.md#check-it-yourself), run:

```sh
python3 scripts/check-statement-audit.py
python3 scripts/check-artifacts.py
```

The first command validates input hashes, builds the original targets and the
supplementary module, compiles exact-type and defining-equation probes, checks
normalization/domain conversions, and reads the axiom closures of all three
targets and three bridge results. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted. It removes temporary Lean sources and saves fresh
logs and `result.json` in `.lake/statement-audit/`; failure exits nonzero.
Full reruns clear prior PASS records, and failures record `status: failed`.
A changed-input negative control checked this behavior.

`--hashes-only` skips Lean and checks input identity. The artifact checker
also validates exact declaration-range hashes and the prepared
[Physlib contribution](../Contributions/Physlib/README.md). These mechanical
checks cannot decide whether an informal statement means the same thing as a
Lean statement: that requires reading the source, definitions, and findings.

<details>
<summary>Complete expanded binder table (main/relative; add the three order binders for Rényi)</summary>

| Expanded binder | Bin | Source basis |
| --- | --- | --- |
| `H.Qudit.Norm.norm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Add.add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddSemigroup.add_assoc` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Zero.zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddZeroClass.zero_add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddZeroClass.add_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddMonoid.nsmul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddMonoid.nsmul_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddMonoid.nsmul_succ` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Neg.neg` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Sub.sub` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SubNegMonoid.sub_eq_add_neg` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SubNegMonoid.zsmul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SubNegMonoid.zsmul_zero'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SubNegMonoid.zsmul_succ'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SubNegMonoid.zsmul_neg'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddGroup.neg_add_cancel` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.AddCommMagma.add_comm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Dist.dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.dist_self` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.dist_comm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.dist_triangle` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.edist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.edist_dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.toUniformSpace` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.uniformity_dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.toBornology` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.PseudoMetricSpace.cobounded_sets` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.MetricSpace.eq_of_dist_eq_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.NormedAddCommGroup.dist_eq` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SMul.smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.SemigroupAction.mul_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.MulAction.one_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.DistribMulAction.smul_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.DistribMulAction.smul_add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Module.add_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Module.zero_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.NormedSpace.norm_smul_le` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Inner.inner` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.InnerProductSpace.norm_sq_eq_re_inner` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.InnerProductSpace.conj_inner_symm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.InnerProductSpace.add_left` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.InnerProductSpace.smul_left` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.CompleteSpace.complete` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Qudit.Module.Finite.fg_top` | STANDING | §1.1, finite complex Hilbert-space structure |
| `H.Nontrivial.exists_pair_ne` | STANDING | Nonzero quantum-system convention |
| `K.Qudit.Norm.norm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Add.add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddSemigroup.add_assoc` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Zero.zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddZeroClass.zero_add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddZeroClass.add_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddMonoid.nsmul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddMonoid.nsmul_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddMonoid.nsmul_succ` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Neg.neg` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Sub.sub` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SubNegMonoid.sub_eq_add_neg` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SubNegMonoid.zsmul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SubNegMonoid.zsmul_zero'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SubNegMonoid.zsmul_succ'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SubNegMonoid.zsmul_neg'` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddGroup.neg_add_cancel` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.AddCommMagma.add_comm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Dist.dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.dist_self` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.dist_comm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.dist_triangle` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.edist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.edist_dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.toUniformSpace` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.uniformity_dist` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.toBornology` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.PseudoMetricSpace.cobounded_sets` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.MetricSpace.eq_of_dist_eq_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.NormedAddCommGroup.dist_eq` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SMul.smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.SemigroupAction.mul_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.MulAction.one_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.DistribMulAction.smul_zero` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.DistribMulAction.smul_add` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Module.add_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Module.zero_smul` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.NormedSpace.norm_smul_le` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Inner.inner` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.InnerProductSpace.norm_sq_eq_re_inner` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.InnerProductSpace.conj_inner_symm` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.InnerProductSpace.add_left` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.InnerProductSpace.smul_left` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.CompleteSpace.complete` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Qudit.Module.Finite.fg_top` | STANDING | §1.1, finite complex Hilbert-space structure |
| `K.Nontrivial.exists_pair_ne` | STANDING | Nonzero quantum-system convention |
| `N.AddHom.toFun` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `N.AddHom.map_add'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `N.MulActionHom.map_smul'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `N.CompletelyPositiveMap.map_cstarMatrix_nonneg'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `N.QuantumChannel.CPTP.trace_map` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `M.AddHom.toFun` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `M.AddHom.map_add'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `M.MulActionHom.map_smul'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `M.CompletelyPositiveMap.map_cstarMatrix_nonneg'` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `M.QuantumChannel.CPTP.trace_map` | SOURCE | Theorem 1 / Eq. (1.5), channel definition |
| `H` | TYPING | §1.1, space carrier |
| `K` | TYPING | §1.1, space carrier |

The JSON preserves the displayed inherited types and defaults, as well as a complete expanded table for each target.

</details>
