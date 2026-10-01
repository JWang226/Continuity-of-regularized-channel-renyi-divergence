/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.RegularizationIdentities
import QuantumChannelContinuity.ExtendedFekete

/-!
# Identification of block suprema with the manuscript's limits

Tensor additivity and superadditivity also hold below one, including the
orthogonal-support infinite convention. Extended Fekete then identifies the
actual regularized quantities with their normalized block limits at every
admissible Rényi order.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B : Type u} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

/-- The finite formula below one uses nonzero overlap, not support inclusion. -/
theorem stateRenyi_eq_formula_lt {p : ℝ} (hp : p < 1)
    (ρ σ : DensityState A) (hQ : (sandwichedQuasi p ρ.op σ.op).re ≠ 0) :
    stateRenyi p ρ σ =
      ((1 / (p - 1)) * Real.logb 2 (sandwichedQuasi p ρ.op σ.op).re : ℝ) := by
  simp only [stateRenyi, sandwichedRenyiDivNN, not_lt.mpr hp.le, false_and,
    hQ, and_false, or_false, ↓reduceIte, toBits_coe]
  rw [sandwichedRenyiDiv, ρ.trace_one]
  simp only [Complex.one_re, div_one, Real.logb]
  congr 1
  ring

theorem stateRenyi_eq_top_of_zero_quasi {p : ℝ} (hp : p < 1)
    (ρ σ : DensityState A) (hQ : (sandwichedQuasi p ρ.op σ.op).re = 0) :
    stateRenyi p ρ σ = ⊤ := by
  simp [stateRenyi, sandwichedRenyiDivNN, hp, ρ.op_ne_zero, hQ]

/-- Tensor additivity below one, including orthogonal-support infinities. -/
theorem stateRenyi_tensor_lt {p : ℝ} (hhalf : 1 / 2 ≤ p) (hp : p < 1)
    (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRenyi p (ρ.tensor τ) (σ.tensor ω) = stateRenyi p ρ σ + stateRenyi p τ ω := by
  have hQ : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re =
      (sandwichedQuasi p ρ.op σ.op).re * (sandwichedQuasi p τ.op ω.op).re := by
    simp only [DensityState.tensor, sandwichedQuasi_tensor p _ _ _ _
      ρ.nonneg σ.nonneg τ.nonneg ω.nonneg, Complex.mul_re,
      sandwichedQuasi_im_zero, zero_mul, sub_zero]
  by_cases hρQ : (sandwichedQuasi p ρ.op σ.op).re = 0
  · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re = 0 := by
      rw [hQ, hρQ, zero_mul]
    rw [stateRenyi_eq_top_of_zero_quasi hp _ _ hprod,
      stateRenyi_eq_top_of_zero_quasi hp ρ σ hρQ]
    exact (EReal.top_add_of_ne_bot
      (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg hhalf hp.ne τ ω))).symm
  · by_cases hτQ : (sandwichedQuasi p τ.op ω.op).re = 0
    · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re = 0 := by
        rw [hQ, hτQ, mul_zero]
      rw [stateRenyi_eq_top_of_zero_quasi hp _ _ hprod,
        stateRenyi_eq_top_of_zero_quasi hp τ ω hτQ]
      exact (EReal.add_top_of_ne_bot
        (ne_bot_of_le_ne_bot (by simp) (stateRenyi_nonneg hhalf hp.ne ρ σ))).symm
    · have hprod : (sandwichedQuasi p (ρ.tensor τ).op (σ.tensor ω).op).re ≠ 0 := by
        rw [hQ]
        exact mul_ne_zero hρQ hτQ
      rw [stateRenyi_eq_formula_lt hp _ _ hprod,
        stateRenyi_eq_formula_lt hp ρ σ hρQ, stateRenyi_eq_formula_lt hp τ ω hτQ,
        hQ, Real.logb_mul hρQ hτQ, mul_add, EReal.coe_add]

/-- Tensor additivity at every admissible Rényi order other than one. -/
theorem stateRenyi_tensor_admissible {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRenyi p (ρ.tensor τ) (σ.tensor ω) = stateRenyi p ρ σ + stateRenyi p τ ω := by
  rcases lt_or_gt_of_ne hp1 with h | h
  · exact stateRenyi_tensor_lt hp h ρ σ τ ω
  · exact stateRenyi_tensor h ρ σ τ ω

section Channel
variable {A B C D : Type} [Qudit A] [Qudit B] [Qudit C] [Qudit D]
  [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

/-- Stabilized channel superadditivity at every admissible order. -/
theorem channelRenyi_tensor_superadditive_admissible {p : ℝ}
    (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP A B) (K L : CPTP C D) :
    channelRenyi p N M + channelRenyi p K L ≤
      channelRenyi p (tensorChannel N K) (tensorChannel M L) := by
  apply ENNReal.iSup_add_iSup_le
  intro ψ φ
  have h := stateRenyi_le_channel (tensorChannel N K) (tensorChannel M L) p
    (ψ.stabilizedProduct φ)
  rw [amplifiedOutput_product N K, amplifiedOutput_product M L,
    stateRenyi_isometry hp hp1, stateRenyi_tensor_admissible hp hp1,
    EReal.toENNReal_add (stateRenyi_nonneg hp hp1 _ _) (stateRenyi_nonneg hp hp1 _ _)] at h
  exact h

theorem blockRenyi_superadditive_admissible {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) (m n : ℕ) :
    blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (m + n) := by
  have h := channelRenyi_tensor_superadditive_admissible hp hp1
    (channelPower N m) (channelPower M m) (channelPower N n) (channelPower M n)
  have heq := channelRenyi_isometry hp hp1 (powerConcatIso A m n) (powerConcatIso B m n)
    (tensorChannel (channelPower N m) (channelPower N n))
    (tensorChannel (channelPower M m) (channelPower M n))
    (channelPower N (n + m)) (channelPower M (n + m))
    (powerConcat_intertwine N m n) (powerConcat_intertwine M m n)
  rw [heq] at h
  change blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (n + m) at h
  rwa [Nat.add_comm n m] at h

/-- The actual normalized Rényi block sequence converges to its defining
supremum for every admissible order, including infinite values. -/
theorem blockRenyi_tendsto_regularized {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) :
    Tendsto (fun n : ℕ => blockRenyi p N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRenyi p N M)) :=
  ennreal_superadditive_tendsto_iSup_div (blockRenyi p N M)
    (blockRenyi_superadditive_admissible hp hp1 N M)

/-- The actual normalized relative-entropy block sequence converges to its
supremum, including the infinite case. -/
theorem blockRelative_tendsto_regularized (N M : CPTP A B) :
    Tendsto (fun n : ℕ => blockRelative N M n / (n : ℝ≥0∞)) atTop
      (𝓝 (regularizedRelative N M)) :=
  ennreal_superadditive_tendsto_iSup_div (blockRelative N M) (blockRelative_superadditive N M)

/-- Exact block scaling holds below one as well. -/
theorem regularizedRenyi_power_scaling_admissible {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) {n : ℕ} (hn : 0 < n) :
    regularizedRenyi p (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRenyi p N M := by
  simp only [regularizedRenyi, blockRenyi_power hp hp1]
  exact ennreal_iSup_div_multiples (blockRenyi p N M)
    (blockRenyi_superadditive_admissible hp hp1 N M) hn

end Channel
end QuantumChannelContinuity
