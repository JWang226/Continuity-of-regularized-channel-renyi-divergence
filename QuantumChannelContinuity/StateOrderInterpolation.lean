/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.StateOrderPowers

/-! # Three-lines interpolation for weighted quantum trace functionals -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open Complex.HadamardThreeLines
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable def stripExponent (a b : ℝ) (z : ℂ) : ℂ :=
  (1 - z) * (a : ℂ) + z * (b : ℂ)

theorem stripExponent_re (a b : ℝ) (z : ℂ) :
    (stripExponent a b z).re = (1 - z.re) * a + z.re * b := by
  simp [stripExponent, Complex.mul_re]

theorem stripExponent_re_mem (a b : ℝ) {z : ℂ} (hz : z ∈ verticalClosedStrip 0 1) :
    (stripExponent a b z).re ∈ Icc (min a b) (max a b) := by
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  rw [stripExponent_re]
  constructor
  · have h₀ := mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr (min_le_left a b))
    have h₁ := mul_nonneg hz0 (sub_nonneg.mpr (min_le_right a b))
    nlinarith
  · have h₀ := mul_nonneg (sub_nonneg.mpr hz1) (sub_nonneg.mpr (le_max_left a b))
    have h₁ := mul_nonneg hz0 (sub_nonneg.mpr (le_max_right a b))
    nlinarith

/-- The scalar holomorphic duality family used for weighted Schatten
interpolation. Its two exponent paths are affine in the complex strip. -/
noncomputable def operatorTraceFamily (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ) (z : ℂ) : ℂ :=
  Tr (operatorCpow X (stripExponent a₀ a₁ z) * V * R *
    operatorCpow σ (stripExponent b₀ b₁ z))

theorem differentiable_operatorTraceFamily (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ) :
    Differentiable ℂ (operatorTraceFamily X σ V R a₀ a₁ b₀ b₁) := by
  have ha : Differentiable ℂ (stripExponent a₀ a₁) := by unfold stripExponent; fun_prop
  have hb : Differentiable ℂ (stripExponent b₀ b₁) := by unfold stripExponent; fun_prop
  have hprod := ((((differentiable_operatorCpow X).comp ha).mul_const V).mul_const R).mul
    ((differentiable_operatorCpow σ).comp hb)
  exact Tr.toContinuousLinearMap.differentiable.comp hprod

theorem operatorTraceFamily_bounded (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ) :
    BddAbove ((norm ∘ operatorTraceFamily X σ V R a₀ a₁ b₀ b₁) '' verticalClosedStrip 0 1) := by
  obtain ⟨C, hC, hX⟩ := operatorCpow_norm_bounded X (min a₀ a₁) (max a₀ a₁)
  obtain ⟨D, hD, hσ⟩ := operatorCpow_norm_bounded σ (min b₀ b₁) (max b₀ b₁)
  refine ⟨‖(Tr : L H →ₗ[ℂ] ℂ).toContinuousLinearMap‖ * (C * ‖V‖ * ‖R‖ * D), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hzX := stripExponent_re_mem a₀ a₁ hz
  have hzσ := stripExponent_re_mem b₀ b₁ hz
  change ‖Tr (operatorCpow X (stripExponent a₀ a₁ z) * V * R *
    operatorCpow σ (stripExponent b₀ b₁ z))‖ ≤ _
  calc
    _ ≤ ‖(Tr : L H →ₗ[ℂ] ℂ).toContinuousLinearMap‖ *
        ‖operatorCpow X (stripExponent a₀ a₁ z) * V * R * operatorCpow σ (stripExponent b₀ b₁ z)‖ :=
      Tr.toContinuousLinearMap.le_opNorm _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        _ ≤ (‖operatorCpow X (stripExponent a₀ a₁ z)‖ * ‖V‖ * ‖R‖) *
            ‖operatorCpow σ (stripExponent b₀ b₁ z)‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
            (norm_nonneg _))
        _ ≤ _ := mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (hX _ hzX.1 hzX.2) (norm_nonneg _)) (norm_nonneg _))
          (hσ _ hzσ.1 hzσ.2) (norm_nonneg _) (by positivity)

/-- Analyticity and strip boundedness are proved for the actual operator
family. Only its concrete two boundary estimates are needed by Hadamard. -/
theorem operatorTraceFamily_three_lines (X σ V R : L H) (a₀ a₁ b₀ b₁ : ℝ)
    {θ M₀ M₁ : ℝ} (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hleft : ∀ z : ℂ, z.re = 0 → ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ z‖ ≤ M₀)
    (hright : ∀ z : ℂ, z.re = 1 → ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ z‖ ≤ M₁) :
    ‖operatorTraceFamily X σ V R a₀ a₁ b₀ b₁ (θ : ℂ)‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have h := norm_le_interp_of_mem_verticalClosedStrip' (by norm_num : (0 : ℝ) < 1)
    (show (θ : ℂ) ∈ verticalClosedStrip 0 1 from ⟨hθ₀, hθ₁⟩)
    (differentiable_operatorTraceFamily X σ V R a₀ a₁ b₀ b₁).diffContOnCl
    (operatorTraceFamily_bounded X σ V R a₀ a₁ b₀ b₁)
    (fun z hz => hleft z hz) (fun z hz => hright z hz)
  simpa using h

end QuantumChannelContinuity
