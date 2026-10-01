/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.StateOrderPowers
import QuantumChannelContinuity.Schatten

/-! # Faithful polar witnesses for Schatten duality -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

theorem star_mul_self_strictlyPositive {C : L H} (hC : IsUnit C) :
    IsStrictlyPositive (star C * C) :=
  ⟨star_mul_self_nonneg _, hC.star.mul hC⟩

/-- A faithful matrix has an actual unitary right polar factor. -/
theorem exists_right_polar_unitary {C : L H} (hC : IsUnit C) :
    ∃ U : unitary (L H), star (U : QuantumState.L H) * C = CFC.rpow (star C * C) (1 / 2 : ℝ) := by
  let L := star C * C
  have hL : IsStrictlyPositive L := star_mul_self_strictlyPositive hC
  let S := CFC.rpow L (-(1 / 2 : ℝ))
  let U := C * S
  have hS : IsSelfAdjoint S := CFC.rpow_nonneg.isSelfAdjoint
  have hSU : IsUnit U := hC.mul hL.rpow.isUnit
  have hmul (a b : ℝ) : CFC.rpow L a * CFC.rpow L b = CFC.rpow L (a + b) :=
    (CFC.rpow_add hL.isUnit).symm
  have hmul_one (a : ℝ) : CFC.rpow L a * L = CFC.rpow L (a + 1) := by
    calc
      _ = CFC.rpow L a * CFC.rpow L (1 : ℝ) := by rw [show CFC.rpow L 1 = L from CFC.rpow_one _ hL.nonneg]
      _ = _ := hmul a 1
  have hSUU : star U * U = 1 := by
    simp only [U, star_mul, hS.star_eq]
    rw [mul_assoc, ← mul_assoc (star C), show star C * C = L from rfl, ← mul_assoc]
    change CFC.rpow L (-(1 / 2 : ℝ)) * L * CFC.rpow L (-(1 / 2 : ℝ)) = 1
    rw [hmul_one, hmul]
    norm_num
    exact CFC.rpow_zero L hL.nonneg
  have hUSU : U * star U = 1 := by
    apply hSU.mul_right_cancel
    simp only [mul_assoc, hSUU, mul_one, one_mul]
  refine ⟨⟨U, Unitary.mem_iff.mpr ⟨hSUU, hUSU⟩⟩, ?_⟩
  change star U * C = CFC.rpow L (1 / 2 : ℝ)
  simp only [U, star_mul, hS.star_eq, mul_assoc]
  change CFC.rpow L (-(1 / 2 : ℝ)) * L = CFC.rpow L (1 / 2 : ℝ)
  rw [hmul_one]
  norm_num

noncomputable def schattenWeight (C : L H) (p : ℝ) : ℝ :=
  (Tr (CFC.rpow (star C * C) (p / 2))).re

noncomputable def schattenNorm (C : L H) (p : ℝ) : ℝ := schattenWeight C p ^ (1 / p)

theorem schattenWeight_pos {C : L H} (hC : IsUnit C) (p : ℝ) :
    0 < schattenWeight C p := by
  have hp : IsStrictlyPositive (CFC.rpow (star C * C) (p / 2)) :=
    (star_mul_self_strictlyPositive hC).rpow
  exact trace_re_pos_of_ne_zero hp.nonneg hp.isUnit.ne_zero

theorem schattenNorm_pos {C : L H} (hC : IsUnit C) (p : ℝ) : 0 < schattenNorm C p :=
  Real.rpow_pos_of_pos (schattenWeight_pos hC p) _

/-- Trace scaling written over the real scalar field. -/
theorem real_trace_smul (r : ℝ) (A : L H) : (Tr (r • A)).re = r * (Tr A).re := by
  rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- The positive normalized dual density and its polar unitary attain the
Schatten dual pairing on every faithful matrix. -/
theorem exists_faithful_schatten_dual {C : L H} (hC : IsUnit C) {p : ℝ} (hp : 1 < p) :
    ∃ (X : L H) (U : unitary (L H)), IsStrictlyPositive X ∧ (Tr X).re = 1 ∧
      ‖Tr (CFC.rpow X (1 - 1 / p) * star (U : QuantumState.L H) * C)‖ = schattenNorm C p := by
  let L := star C * C
  let Z := schattenWeight C p
  let A := CFC.rpow L (p / 2)
  let X := Z⁻¹ • A
  have hL : IsStrictlyPositive L := star_mul_self_strictlyPositive hC
  have hA : IsStrictlyPositive A := hL.rpow
  have hZ : 0 < Z := schattenWeight_pos hC p
  have hp0 : 0 < p := by linarith
  have hX : IsStrictlyPositive X := IsStrictlyPositive.smul (inv_pos.mpr hZ) hA
  obtain ⟨U, hU⟩ := exists_right_polar_unitary hC
  refine ⟨X, U, hX, ?_, ?_⟩
  · change (Tr (Z⁻¹ • A)).re = 1
    rw [real_trace_smul]
    change Z⁻¹ * Z = 1
    exact inv_mul_cancel₀ hZ.ne'
  · have hpow : CFC.rpow X (1 - 1 / p) =
        (Z⁻¹) ^ (1 - 1 / p) • CFC.rpow L ((p / 2) * (1 - 1 / p)) := by
      change CFC.rpow (Z⁻¹ • A) (1 - 1 / p) = _
      calc
        _ = (Z⁻¹) ^ (1 - 1 / p) • CFC.rpow A (1 - 1 / p) :=
          operator_rpow_smul A ((LinearMap.nonneg_iff_isPositive A).mp hA.nonneg)
            (inv_nonneg.mpr hZ.le) (1 - 1 / p)
        _ = _ := by
          congr 1
          exact CFC.rpow_rpow L (p / 2) (1 - 1 / p) hL.isUnit (by positivity) hL.nonneg
    have hprod : CFC.rpow X (1 - 1 / p) * star (U : QuantumState.L H) * C =
        (Z⁻¹) ^ (1 - 1 / p) • A := by
      rw [mul_assoc, hU, hpow, smul_mul_assoc]
      congr 1
      calc
        _ = CFC.rpow L ((p / 2) * (1 - 1 / p) + 1 / 2) := (CFC.rpow_add hL.isUnit).symm
        _ = A := by congr 1; field_simp; ring
    have hscalar : (Z⁻¹) ^ (1 - 1 / p) * Z = Z ^ (1 / p) := by
      calc
        _ = Z ^ (-(1 - 1 / p)) * Z ^ (1 : ℝ) := by
          rw [Real.rpow_one, Real.rpow_neg hZ.le, Real.inv_rpow hZ.le]
        _ = Z ^ (-(1 - 1 / p) + 1) := (Real.rpow_add hZ _ _).symm
        _ = Z ^ (1 / p) := by congr 1; ring
    have hpos : 0 ≤ Tr ((Z⁻¹) ^ (1 - 1 / p) • A) :=
      ((LinearMap.nonneg_iff_isPositive _).mp
        (smul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hZ.le) _) hA.nonneg)).trace_nonneg
    have hnorm : ‖Tr ((Z⁻¹) ^ (1 - 1 / p) • A)‖ = (Tr ((Z⁻¹) ^ (1 - 1 / p) • A)).re := by
      simpa only [Complex.ofReal_re] using (congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hpos)).symm
    rw [hprod, hnorm, real_trace_smul]
    exact hscalar

end QuantumChannelContinuity
