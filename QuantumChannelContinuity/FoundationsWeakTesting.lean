/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.FoundationsTesting
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # Concrete Umegaki weak testing bound -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
variable {H : Type} [Qudit H] [Nontrivial H]

/-- The standard binary entropy bound applied to the actual POVM probabilities. -/
theorem binary_entropy_lower (M : POVM H (Fin 2)) (ρ : DensityState H) :
    -Real.log 2 ≤ M.probability ρ 0 * Real.log (M.probability ρ 0) +
      M.probability ρ 1 * Real.log (M.probability ρ 1) := by
  have hsum := M.sum_probability ρ
  rw [Fin.sum_univ_two] at hsum
  have hp1 : 1 - M.probability ρ 0 = M.probability ρ 1 := by linarith
  have h := Real.binEntropy_le_log_two (p := M.probability ρ 0)
  rw [Real.binEntropy, hp1, Real.log_inv, Real.log_inv] at h
  linarith

/-- Binary Umegaki data processing yields the one-outcome testing lower bound,
including singular states and the support-mismatch case. -/
theorem measured_relative_lower (M : POVM H (Fin 2)) (ρ σ : DensityState H) :
    (-1 - M.probability ρ 0 * Real.logb 2 (M.probability σ 0) : ℝ) ≤
      stateRelative ρ σ := by
  by_cases hs : suppLE ρ.op σ.op
  · have hsE := suppLE_of_CPTP M.channel ρ.nonneg σ.nonneg hs
    have hmeas := stateRelative_dataProcessing M.channel ρ σ
    apply le_trans _ hmeas
    rw [umegaki_common_eigenbasis (EuclideanSpace.basisFun (Fin 2) ℂ)
      (ρ.map M.channel) (σ.map M.channel) (M.probability ρ) (M.probability σ)
      (M.channel_apply_basis_probability ρ) (M.channel_apply_basis_probability σ) hsE,
      EReal.coe_le_coe_iff, Fin.sum_univ_two, Real.logb]
    apply (le_div_iff₀ log_two_pos).mpr
    have he := binary_entropy_lower M ρ
    have hq := Real.log_nonpos (M.probability_nonneg σ 1) (M.probability_le_one σ 1)
    have hneg := mul_nonpos_of_nonneg_of_nonpos (M.probability_nonneg ρ 1) hq
    have hcancel : (M.probability ρ 0 * (Real.log (M.probability σ 0) / Real.log 2)) * Real.log 2 =
        M.probability ρ 0 * Real.log (M.probability σ 0) := by
      field_simp [ne_of_gt log_two_pos]
    nlinarith
  · rw [stateRelative_eq_top_of_not_support ρ σ hs]
    exact le_top

/-- The actual binary quantum test supplies the weak-testing logarithmic
inequality required by the manuscript, with no quantum assumptions remaining. -/
theorem binary_relative_testing_log (T : Effect H) (ρ σ : DensityState H)
    {ell a : ℝ} (hD : stateRelative ρ σ ≤ (a : EReal))
    (hpay : 0 < T.probability ρ - (2 : ℝ) ^ ell * T.probability σ) :
    ell * T.probability ρ - 1 ≤ a := by
  let M := binaryPOVM T.op T.nonneg T.le_one
  have hpdef : M.probability ρ 0 = T.probability ρ := by
    simp [M, POVM.probability, Effect.probability, binaryPOVM]
  have hqdef : M.probability σ 0 = T.probability σ := by
    simp [M, POVM.probability, Effect.probability, binaryPOVM]
  have hp : 0 < T.probability ρ := lt_of_le_of_lt
    (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (T.probability_nonneg σ)) (sub_pos.mp hpay)
  have hs : suppLE ρ.op σ.op := (stateRelative_ne_top_iff ρ σ).mp (by
    intro htop
    rw [htop] at hD
    exact (not_le_of_gt (EReal.coe_lt_top a)) hD)
  have hq : 0 < T.probability σ := by
    rw [← hqdef]
    exact M.probability_pos_of_support ρ σ hs 0 (hpdef.symm ▸ hp)
  have hlog : ell + Real.logb 2 (T.probability σ) ≤ 0 := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (mul_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell) hq)
      ((sub_pos.mp hpay).le.trans (T.probability_le_one ρ))
    rw [Real.logb_mul (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ell).ne' hq.ne',
      Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1), Real.logb_one] at h
    exact h
  have hlow := (measured_relative_lower M ρ σ).trans hD
  rw [EReal.coe_le_coe_iff, hpdef, hqdef] at hlow
  nlinarith

/-- The complete concrete Umegaki weak bound at any strictly positive rate. -/
theorem binary_relative_testing_bound (T : Effect H) (ρ σ : DensityState H)
    {ell a : ℝ} (hell : 0 < ell) (hD : stateRelative ρ σ ≤ (a : EReal)) :
    T.probability ρ - (2 : ℝ) ^ ell * T.probability σ ≤ a / ell + 1 / ell := by
  have ha : 0 ≤ a := EReal.coe_nonneg.mp ((stateRelative_nonneg ρ σ).trans hD)
  have hob : T.probability ρ - (2 : ℝ) ^ ell * T.probability σ ≤ T.probability ρ :=
    sub_le_self _ (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (T.probability_nonneg σ))
  have h := ChannelContinuity.weak_testing_bound_of_positive_payoff
    (n := 1) (r := ell) (d := a) (by norm_num) hell ha hob (fun hpay => by
      simpa using binary_relative_testing_log T ρ σ hD hpay)
  simpa using h

/-- The concrete weak bound passes to the supremum over all acceptance tests. -/
theorem stateHockey_relative_bound (ρ σ : DensityState H) {ell a : ℝ}
    (hell : 0 < ell) (hD : stateRelative ρ σ ≤ (a : EReal)) :
    stateHockey ((2 : ℝ) ^ ell) ρ σ ≤ a / ell + 1 / ell := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T, rfl⟩
  exact binary_relative_testing_bound T ρ σ hell hD

end QuantumChannelContinuity
