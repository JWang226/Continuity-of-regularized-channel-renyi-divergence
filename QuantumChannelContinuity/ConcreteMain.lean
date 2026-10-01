/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.Regularization
import QuantumChannelContinuity.FoundationsInfiniteLimit
import ChannelContinuity.Main

/-!
# Continuity for concrete channel divergences, with residual inputs exposed

Unlike the original scalar-only theorem, all states, channels, tensor powers,
regularized quantities and testing functions here are defined quantum objects.
The testing assumptions are discharged by proved quantum measurement bounds.
This module retains a raw-estimate interface. `QuantumMain.lean` constructs
that estimate from the remaining explicitly named quantum premises.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ENNReal Topology TensorProduct

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- Exact residual inputs for the finite right-limit argument. This is a
conditional interface, not an assertion that its fields have been constructed
for every channel pair. The regularized three-piece estimate is an input here;
`QuantumThresholdInputs.toRemaining` constructs it in `QuantumMain.lean`. -/
structure RemainingFiniteInputs (N M : CPTP H K) where
  relative_finite : regularizedRelative N M ≠ ⊤
  renyi_finite : ∀ α, 1 < α → regularizedRenyi α N M ≠ ⊤
  order_mono : MonotoneOn (fun α => (regularizedRenyi α N M).toReal) (Ioi 1)
  relative_le_renyi : ∀ α, 1 < α →
    (regularizedRelative N M).toReal ≤ (regularizedRenyi α N M).toReal
  cap : ℝ
  raw_schatten :
    let a := fun α => (regularizedRenyi α N M).toReal
    let dPlus := sInf (a '' Ioi 1)
    ∀ r, 0 ≤ r → r < dPlus → ∀ t : ℝ, 1 ≤ t →
      ∀ n : ℕ, t < (n : ℝ) → 2 * t ≤ (n : ℝ) →
      (2 : ℝ) ^ (t * dPlus / 2) ≤
        ChannelContinuity.rawSchattenRhs n t r dPlus cap
          (Real.sqrt (blockTesting N M n r))
          (Real.sqrt (blockTesting N M n (dPlus + 1 / (t * t))))

/-- Construct the analytical input record with all quantum testing fields
proved from the concrete channel definitions. -/
noncomputable def RemainingFiniteInputs.analytic {N M : CPTP H K}
    (h : RemainingFiniteInputs N M) : ChannelContinuity.FiniteAnalyticInputs where
  d := (regularizedRelative N M).toReal
  renyi α := (regularizedRenyi α N M).toReal
  cap := h.cap
  testing := blockTesting N M
  d_nonneg := ENNReal.toReal_nonneg
  order_mono := h.order_mono
  relative_le_renyi := h.relative_le_renyi
  testing_nonneg := blockTesting_nonneg N M
  weak_testing _ hr _ hn := regularized_weak_testing N M h.relative_finite hn hr
  renyi_testing α hα ell _ _ hn :=
    regularized_renyi_testing N M hα (h.renyi_finite α hα) hn ell
  raw_schatten := h.raw_schatten

/-- The concrete block-supremum Rényi divergence is right-continuous at one
once the explicitly listed residual finite-case inputs are proved. -/
theorem regularized_right_continuity_of_remaining {N M : CPTP H K}
    (h : RemainingFiniteInputs N M) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[>] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h.analytic.right_continuity
  change Tendsto (fun α => ENNReal.ofReal ((regularizedRenyi α N M).toReal))
    (𝓝[>] (1 : ℝ)) (𝓝 (ENNReal.ofReal ((regularizedRelative N M).toReal))) at hlim
  rw [ENNReal.ofReal_toReal h.relative_finite] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact ENNReal.ofReal_toReal (h.renyi_finite α hα)

/-- A positive block length and an actual pure input to its stabilized channel. -/
abbrev BlockInput (H : Type) [Qudit H] [Nontrivial H] :=
  (n : {n : ℕ // 0 < n}) ×
    PureInput (TensorPower H n.val ⊗[ℂ] TensorPower H n.val)

noncomputable def inputRenyi (N M : CPTP H K) (α : ℝ) (i : BlockInput H) : ℝ≥0∞ :=
  (stateRenyi α (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).toENNReal / (i.1.val : ℝ≥0∞)

noncomputable def inputRelative (N M : CPTP H K) (i : BlockInput H) : ℝ≥0∞ :=
  (stateRelative (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).toENNReal / (i.1.val : ℝ≥0∞)

theorem regularizedRenyi_eq_input_sup (N M : CPTP H K) (α : ℝ) :
    regularizedRenyi α N M = ⨆ i : BlockInput H, inputRenyi N M α i := by
  simp only [regularizedRenyi, blockRenyi, channelRenyi, ENNReal.iSup_div,
    inputRenyi, iSup_sigma, iSup_subtype]

theorem regularizedRelative_eq_input_sup (N M : CPTP H K) :
    regularizedRelative N M = ⨆ i : BlockInput H, inputRelative N M i := by
  simp only [regularizedRelative, blockRelative, channelRelative, ENNReal.iSup_div,
    inputRelative, iSup_sigma, iSup_subtype]

/-- The two-sided finite-case conclusion for actual channel quantities.
The only left-side inputs are explicitly pointwise order monotonicity and
order-one limits of the actual normalized block-output divergences. -/
theorem theorem_one_concrete_finite_conditional {N M : CPTP H K}
    (h : RemainingFiniteInputs N M)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) ChannelContinuity.LeftOrders)
    (hstate : ∀ i : BlockInput H,
      Tendsto (fun α => inputRenyi N M α i) (𝓝[<] (1 : ℝ)) (𝓝 (inputRelative N M i))) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  simp_rw [regularizedRenyi_eq_input_sup, regularizedRelative_eq_input_sup]
  apply ChannelContinuity.regularized_continuity_of_right_continuity hmono hstate
  simpa only [← regularizedRenyi_eq_input_sup, ← regularizedRelative_eq_input_sup] using
    regularized_right_continuity_of_remaining h

/-- A concrete support-mismatched output is the infinite witness required by
the analytical proof, including its positive block-length normalization. -/
theorem input_top_of_support_mismatch (N M : CPTP H K) (i : BlockInput H)
    (hs : ¬ suppLE (amplifiedOutput (channelPower N i.1.val) i.2.density).op
      (amplifiedOutput (channelPower M i.1.val) i.2.density).op) :
    inputRelative N M i = ⊤ ∧ ∀ α, 1 < α → inputRenyi N M α i = ⊤ := by
  constructor
  · simp [inputRelative, stateRelative_eq_top_of_not_support _ _ hs, ENNReal.top_div]
  · intro α hα
    simp [inputRenyi, stateRenyi_eq_top_of_not_support hα _ _ hs, ENNReal.top_div]

/-- The complete infinite-witness branch for actual channel tensor powers.
There are no extra state-limit, order-monotonicity or filter assumptions:
a concrete support-mismatched block output suffices. -/
theorem theorem_one_of_support_mismatch (N M : CPTP H K) (i : BlockInput H)
    (hs : ¬ suppLE (amplifiedOutput (channelPower N i.1.val) i.2.density).op
      (amplifiedOutput (channelPower M i.1.val) i.2.density).op) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  obtain ⟨hD, hα⟩ := input_top_of_support_mismatch N M i hs
  have htop : regularizedRelative N M = ⊤ := by
    rw [regularizedRelative_eq_input_sup]
    exact ChannelContinuity.regularized_eq_top_of_witness (inputRelative N M) hD
  rw [htop, ← nhdsLT_sup_nhdsGT]
  apply Filter.Tendsto.sup
  · have hsleft := stateRenyi_tendsto_top_left_of_not_support _ _ hs
    have hen : Tendsto (fun α =>
        (stateRenyi α (amplifiedOutput (channelPower N i.1.val) i.2.density)
          (amplifiedOutput (channelPower M i.1.val) i.2.density)).toENNReal)
        (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
      simpa only [Function.comp_def, EReal.toENNReal_top] using
        (EReal.continuous_toENNReal.tendsto ⊤).comp hsleft
    have hi : Tendsto (fun α => inputRenyi N M α i) (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
      have hdiv := ENNReal.Tendsto.div_const (b := (i.1.val : ℝ≥0∞)) hen
        (Or.inl (by simp))
      simpa only [inputRenyi, ENNReal.top_div, ENNReal.natCast_ne_top, ↓reduceIte] using hdiv
    apply tendsto_nhds_top_mono' hi
    intro α
    change inputRenyi N M α i ≤ regularizedRenyi α N M
    rw [regularizedRenyi_eq_input_sup]
    exact le_iSup (inputRenyi N M α) i
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα1
    rw [regularizedRenyi_eq_input_sup]
    exact (ChannelContinuity.regularized_eq_top_of_witness
      (inputRenyi N M α) (hα α hα1)).symm

/-- Theorem 1's exact two-sided extended-real conclusion for actual CPTP
channels, conditional on precisely exposed finite-case or infinite-witness
inputs and the remaining pointwise left-order prerequisites. -/
theorem theorem_one_concrete_conditional {N M : CPTP H K}
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) ChannelContinuity.LeftOrders)
    (hstate : ∀ i : BlockInput H,
      Tendsto (fun α => inputRenyi N M α i) (𝓝[<] (1 : ℝ)) (𝓝 (inputRelative N M i)))
    (hcases : Nonempty (RemainingFiniteInputs N M) ∨
      ∃ i : BlockInput H,
        ¬ suppLE (amplifiedOutput (channelPower N i.1.val) i.2.density).op
          (amplifiedOutput (channelPower M i.1.val) i.2.density).op) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  rcases hcases with h | ⟨i, hs⟩
  · obtain ⟨h⟩ := h
    exact theorem_one_concrete_finite_conditional h hmono hstate
  · exact theorem_one_of_support_mismatch N M i hs

end QuantumChannelContinuity
