import QuantumChannelContinuity.StateSupportLimits
import Mathlib.Analysis.Complex.Hadamard

/-! # Analytic operator powers for weighted Schatten interpolation -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- Complex powers of a faithful positive operator, defined by its actual
operator logarithm. -/
noncomputable def operatorCpow (A : L H) (z : ℂ) : L H :=
  NormedSpace.exp (z • CFC.log A)

theorem operatorCpow_ofReal {A : L H} (hA : IsStrictlyPositive A) (t : ℝ) :
    operatorCpow A (t : ℂ) = CFC.rpow A t := by
  rw [CFC.rpow_eq_normedSpace_exp_smul_log hA]
  unfold operatorCpow
  rw [Complex.coe_smul]

theorem operatorCpow_zero (A : L H) : operatorCpow A 0 = 1 := by
  simp [operatorCpow]

theorem operatorCpow_add (A : L H) (z w : ℂ) :
    operatorCpow A (z + w) = operatorCpow A z * operatorCpow A w := by
  letI : NormedAlgebra ℚ (L H) := .restrictScalars ℚ ℂ (L H)
  unfold operatorCpow
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (CFC.log A)).smul_left z).smul_right w)

theorem star_operatorCpow (A : L H) (z : ℂ) :
    star (operatorCpow A z) = operatorCpow A (star z) := by
  unfold operatorCpow
  have hlog : IsSelfAdjoint (CFC.log A) := cfc_predicate _ _
  rw [NormedSpace.star_exp, star_smul, hlog.star_eq]

theorem operatorCpow_star_mul {A : L H} (hA : IsStrictlyPositive A) (z : ℂ) :
    star (operatorCpow A z) * operatorCpow A z = CFC.rpow A (2 * z.re) := by
  rw [star_operatorCpow, ← operatorCpow_add]
  have hz : star z + z = ((2 * z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp <;> ring
  rw [hz, operatorCpow_ofReal hA]

theorem operatorCpow_mul_star {A : L H} (hA : IsStrictlyPositive A) (z : ℂ) :
    operatorCpow A z * star (operatorCpow A z) = CFC.rpow A (2 * z.re) := by
  rw [star_operatorCpow, ← operatorCpow_add, add_comm]
  have hz : star z + z = ((2 * z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp <;> ring
  rw [hz, operatorCpow_ofReal hA]

theorem differentiable_operatorCpow (A : L H) : Differentiable ℂ (operatorCpow A) := by
  intro z
  exact (hasDerivAt_exp_smul_const (CFC.log A) z).differentiableAt

theorem operatorCpow_imaginary_mem_unitary (A : L H) (t : ℝ) :
    operatorCpow A ((t : ℂ) * Complex.I) ∈ unitary (L H) := by
  rw [Unitary.mem_iff, star_operatorCpow, ← operatorCpow_add, ← operatorCpow_add]
  have hneg : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by simp
  simp [hneg, operatorCpow_zero]

/-- Imaginary powers do not change the operator norm. -/
theorem norm_operatorCpow_eq_re (A : L H) (z : ℂ) :
    ‖operatorCpow A z‖ = ‖operatorCpow A (z.re : ℂ)‖ := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [operatorCpow_add]
  exact CStarRing.norm_mul_mem_unitary _ (operatorCpow_imaginary_mem_unitary A z.im)

/-- The complex power has bounded norm on every closed vertical strip.
This uses compactness only in the real direction. -/
theorem operatorCpow_norm_bounded (A : L H) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖operatorCpow A z‖ ≤ C := by
  have hc : Continuous (fun t : ℝ => ‖operatorCpow A (t : ℂ)‖) :=
    ((differentiable_operatorCpow A).continuous.comp Complex.continuous_ofReal).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hc).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz₀ hz₁
  rw [norm_operatorCpow_eq_re]
  exact (hC ⟨z.re, ⟨hz₀, hz₁⟩, rfl⟩).trans (le_max_left _ _)

end QuantumChannelContinuity
