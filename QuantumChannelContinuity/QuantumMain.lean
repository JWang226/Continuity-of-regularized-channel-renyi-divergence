/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.ConcreteMain
import QuantumChannelContinuity.ThreePieceExponential
import QuantumChannelContinuity.DilationExistence

/-!
# Intermediate continuity interface with the filter–Schatten estimate discharged

This modular interface lists state/order facts, exact CP-slack attainment,
a block CP cap, and scaling under channel powers. The later
`ContinuityAssembly.lean` constructs these inputs from state-order
monotonicity. The regularized three-piece Schatten estimate is derived here.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

noncomputable def rightThreshold (N M : CPTP H K) : ℝ :=
  sInf ((fun α => (regularizedRenyi α N M).toReal) '' Ioi 1)

/-- Concrete inputs for the modular threshold argument. There is no
Schatten, Stinespring, filter-error, tensor-word or raw three-piece field.
`ContinuityAssembly.lean` constructs this record from state-order monotonicity. -/
structure QuantumThresholdInputs (N M : CPTP H K) where
  relative_finite : regularizedRelative N M ≠ ⊤
  renyi_finite : ∀ α, 1 < α → regularizedRenyi α N M ≠ ⊤
  order_mono : MonotoneOn (fun α => (regularizedRenyi α N M).toReal) (Ioi 1)
  relative_le_renyi : ∀ α, 1 < α →
    (regularizedRelative N M).toReal ≤ (regularizedRenyi α N M).toReal
  cap : ℝ
  threshold_le_cap : rightThreshold N M ≤ cap
  block_cap : ∀ n : ℕ, CPLe (channelPower N n).toLinearMap
    (((2 : ℝ) ^ ((n : ℝ) * (cap + 1))) • (channelPower M n).toLinearMap)
  block_slack : ∀ (n : ℕ) (γ : ℝ), 1 ≤ γ →
    HockeySlackAttainment γ (channelPower N n) (channelPower M n)
  power_scaling : ∀ α, 1 < α → α ≤ 2 → ∀ n : ℕ, 0 < n →
    regularizedRenyi α (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRenyi α N M

/-- The infimum threshold is below every admissible order. -/
theorem QuantumThresholdInputs.threshold_le {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) {α : ℝ} (hα : 1 < α) :
    rightThreshold N M ≤ (regularizedRenyi α N M).toReal := by
  apply csInf_le
  · refine ⟨(regularizedRelative N M).toReal, ?_⟩
    rintro _ ⟨β, hβ, rfl⟩
    exact h.relative_le_renyi β hβ
  · exact ⟨α, hα, rfl⟩

/-- Derivation of the exact raw estimate used by the threshold proof.
All filters and dilations are constructed, and the regularized Schatten bound
is applied to the actual `n`-block channels. -/
theorem QuantumThresholdInputs.raw_schatten {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) (r : ℝ) (hr : 0 ≤ r)
    (hgap : r < rightThreshold N M) (t : ℝ) (ht : 1 ≤ t)
    (n : ℕ) (htn : t < (n : ℝ)) (h2tn : 2 * t ≤ (n : ℝ)) :
    (2 : ℝ) ^ (t * rightThreshold N M / 2) ≤
      ChannelContinuity.rawSchattenRhs n t r (rightThreshold N M) h.cap
        (Real.sqrt (blockTesting N M n r))
        (Real.sqrt (blockTesting N M n (rightThreshold N M + 1 / (t * t)))) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hnpos : 0 < (n : ℝ) := htpos.trans htn
  have hn : 0 < n := by exact_mod_cast hnpos
  let p : ℝ := (n : ℝ) / ((n : ℝ) - t)
  have hp : 1 < p := ChannelContinuity.renyi_order_gt_one htpos htn
  have hp2 : p ≤ 2 := ChannelContinuity.renyi_order_le_two htn h2tn
  have hpinv : 1 / p = 1 - t / (n : ℝ) := by
    dsimp [p]
    field_simp
  have hpfrac : (p - 1) / (2 * p) = t / (n : ℝ) / 2 := by
    rw [show (p - 1) / (2 * p) = ((p - 1) / p) / 2 by ring]
    rw [ChannelContinuity.renyi_order_fraction htpos htn]
  let γlow : ℝ := (2 : ℝ) ^ ((n : ℝ) * r)
  let γhigh : ℝ := (2 : ℝ) ^ ((n : ℝ) * (rightThreshold N M + 1 / (t * t)))
  let C : ℝ := (2 : ℝ) ^ ((n : ℝ) * (h.cap + 1))
  have hγlow : 0 ≤ γlow := Real.rpow_nonneg (by norm_num) _
  have hγlow1 : 1 ≤ γlow :=
    Real.one_le_rpow (by norm_num) (mul_nonneg hnpos.le hr)
  have hγle : γlow ≤ γhigh := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    have hi : 0 < 1 / (t * t) := one_div_pos.mpr (mul_pos htpos htpos)
    linarith
  have hγC : γhigh ≤ C := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    apply mul_le_mul_of_nonneg_left _ hnpos.le
    have hi : 1 / (t * t) ≤ 1 := (div_le_one (mul_pos htpos htpos)).2 (by nlinarith)
    linarith [h.threshold_le_cap]
  obtain ⟨E, hE, hEne, V, hV⟩ := cptp_has_nontrivial_dilation (channelPower N n)
  letI := hE
  letI := hEne
  have hcap : CPLe (channelPower N n).toLinearMap ((C : ℂ) • (channelPower M n).toLinearMap) := by
    have heq : (C : ℂ) • (channelPower M n).toLinearMap = C • (channelPower M n).toLinearMap :=
      IsScalarTower.algebraMap_smul ℂ C (channelPower M n).toLinearMap
    rw [heq]
    exact h.block_cap n
  have hS := (hockey_three_piece_regularized_exponential
    (channelPower N n) (channelPower M n) V γlow γhigh C hγlow hγle hγC hV hcap
    (h.block_slack n γlow hγlow1) (h.block_slack n γhigh (hγlow1.trans hγle)) hp hp2).2
  rw [h.power_scaling p hp hp2 n hn, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    hpfrac, hpinv] at hS
  have hexp : t / (n : ℝ) / 2 * ((n : ℝ) * (regularizedRenyi p N M).toReal) =
      t * (regularizedRenyi p N M).toReal / 2 := by
    field_simp
  rw [hexp] at hS
  calc
    (2 : ℝ) ^ (t * rightThreshold N M / 2) ≤
        (2 : ℝ) ^ (t * (regularizedRenyi p N M).toReal / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (h.threshold_le hp) htpos.le) (by norm_num)
    _ ≤ _ := by
      simpa only [ChannelContinuity.rawSchattenRhs, blockTesting, γlow, γhigh, C] using hS

/-- The old scalar/raw interface is now constructed from precise concrete
quantum premises, using the proved filter–Schatten estimate. -/
noncomputable def QuantumThresholdInputs.toRemaining {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) : RemainingFiniteInputs N M where
  relative_finite := h.relative_finite
  renyi_finite := h.renyi_finite
  order_mono := h.order_mono
  relative_le_renyi := h.relative_le_renyi
  cap := h.cap
  raw_schatten := h.raw_schatten

/-- Concrete right continuity, with no assumed Schatten or filtering estimate. -/
theorem regularized_right_continuity_from_quantum_inputs {N M : CPTP H K}
    (h : QuantumThresholdInputs N M) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[>] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) :=
  regularized_right_continuity_of_remaining h.toRemaining


end QuantumChannelContinuity
