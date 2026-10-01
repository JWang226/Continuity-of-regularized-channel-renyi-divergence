/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.StateOrderPowers

/-! # Boundary densities for the analytic interpolation family -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

theorem operatorCpow_unitary_density {X : L H} (hX : IsStrictlyPositive X)
    (U : unitary (L H)) (z : ℂ) :
    (operatorCpow X z * star (U : L H)) * star (operatorCpow X z * star (U : L H)) =
      CFC.rpow X (2 * z.re) := by
  rw [star_mul, star_star, mul_assoc, ← mul_assoc (star (U : L H)), Unitary.coe_star_mul_self,
    one_mul, operatorCpow_mul_star hX]

theorem mul_operatorCpow_density {σ : L H} (hσ : IsStrictlyPositive σ) (R : L H) (z : ℂ) :
    (R * operatorCpow σ z) * star (R * operatorCpow σ z) =
      R * CFC.rpow σ (2 * z.re) * star R := by
  rw [star_mul, mul_assoc, ← mul_assoc (operatorCpow σ z), operatorCpow_mul_star hσ, mul_assoc]

theorem mul_operatorCpow_density_eq_re {σ : L H} (hσ : IsStrictlyPositive σ)
    (R : L H) (z : ℂ) :
    (R * operatorCpow σ z) * star (R * operatorCpow σ z) =
      (R * CFC.rpow σ z.re) * star (R * CFC.rpow σ z.re) := by
  rw [mul_operatorCpow_density hσ R z,
    ← operatorCpow_ofReal hσ z.re,
    mul_operatorCpow_density hσ R (z.re : ℂ), Complex.ofReal_re]

/-- Every imaginary boundary translate of the normalized dual power has
Schatten norm exactly one at the conjugate exponent. -/
theorem normalized_dual_power_trace {X : L H} (hX : IsStrictlyPositive X)
    (hTr : (Tr X).re = 1) (U : unitary (L H)) {q : ℝ} (hq : 1 < q)
    {z : ℂ} (hz : z.re = 1 / q) :
    (Tr (CFC.rpow ((operatorCpow X z * star (U : L H)) *
      star (operatorCpow X z * star (U : L H))) (q / 2))).re ^ (1 / q) = 1 := by
  rw [operatorCpow_unitary_density hX U z, hz]
  have hq0 : 0 < q := by linarith
  have heq : CFC.rpow (CFC.rpow X (2 * (1 / q))) (q / 2) = X := by
    have h := CFC.rpow_rpow X (2 * (1 / q)) (q / 2) hX.isUnit (by positivity) hX.nonneg
    have he : 2 * (1 / q) * (q / 2) = 1 := by field_simp
    rw [he] at h
    exact h.trans (CFC.rpow_one _ hX.nonneg)
  rw [heq, hTr, Real.one_rpow]

end QuantumChannelContinuity
