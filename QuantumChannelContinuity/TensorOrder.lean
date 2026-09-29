import QuantumChannelContinuity.TensorChannels
import QuantumChannelContinuity.Filter

/-!
# Tensor preservation of complete-positive order

These are concrete tensor-superoperator statements for arbitrary finite-dimensional
spaces, not assumptions on an abstract tensor operation.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

/-- Nonnegative real scaling preserves complete positivity. -/
theorem cp_smul {Φ : T A B} (hΦ : IsCompletelyPositive Φ) {c : ℝ} (hc : 0 ≤ c) :
    IsCompletelyPositive (c • Φ) := by
  apply (isCompletelyPositive_iff_cstarMatrix_nonneg _).mpr
  intro k X hX
  have hmap : X.map (c • Φ) = c • X.map Φ := by
    ext i j x
    simp [CStarMatrix.map_apply]
  rw [hmap]
  rw [← algebraMap_smul ℂ c (X.map Φ)]
  exact smul_nonneg (by exact_mod_cast hc : (0 : ℂ) ≤ (c : ℂ))
    ((isCompletelyPositive_iff_cstarMatrix_nonneg _).mp hΦ k X hX)

/-- Exact bilinear identity for the difference of tensor superoperators. -/
theorem tensorSuperoperator_difference (Φ Φ' : T A B) (Ψ Ψ' : T C D) :
    tensorSuperoperator Φ' Ψ' - tensorSuperoperator Φ Ψ =
      tensorSuperoperator (Φ' - Φ) Ψ' + tensorSuperoperator Φ (Ψ' - Ψ) := by
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.sub_apply, LinearMap.add_apply, l_tensor_equiv_symm_tmul,
      tensorSuperoperator_apply]
    ext a c
    simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensor products preserve complete-positive domination. -/
theorem CPLe.tensor {Φ Φ' : T A B} {Ψ Ψ' : T C D}
    (hΦΦ' : CPLe Φ Φ') (hΨΨ' : CPLe Ψ Ψ')
    (hΦ : IsCompletelyPositive Φ) (hΨ' : IsCompletelyPositive Ψ') :
    CPLe (tensorSuperoperator Φ Ψ) (tensorSuperoperator Φ' Ψ') := by
  unfold CPLe
  rw [tensorSuperoperator_difference]
  exact cp_add (tensorSuperoperator_cp _ _ hΦΦ' hΨ')
    (tensorSuperoperator_cp _ _ hΦ hΨΨ')

/-- Scalar tensor factors multiply exactly. -/
theorem tensorSuperoperator_smul (Φ : T A B) (Ψ : T C D) (a b : ℝ) :
    tensorSuperoperator (a • Φ) (b • Ψ) = (a * b) • tensorSuperoperator Φ Ψ := by
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply, LinearMap.smul_apply]
    ext x y
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Tensoring two dominated CP maps multiplies their scalar domination constants. -/
theorem CPLe.tensor_scaled {Φ Φ' : T A B} {Ψ Ψ' : T C D} {a b : ℝ}
    (hΦΦ' : CPLe Φ (a • Φ')) (hΨΨ' : CPLe Ψ (b • Ψ'))
    (hΦ : IsCompletelyPositive Φ) (hΨ' : IsCompletelyPositive Ψ') (hb : 0 ≤ b) :
    CPLe (tensorSuperoperator Φ Ψ) ((a * b) • tensorSuperoperator Φ' Ψ') := by
  rw [← tensorSuperoperator_smul]
  exact hΦΦ'.tensor hΨΨ' hΦ (cp_smul hΨ' hb)

/-- The identity superoperator is completely positive. -/
theorem cp_identity : IsCompletelyPositive (LinearMap.id : T C C) := by
  have h := krausTerm_isCompletelyPositive (LinearMap.id : L C)
  have heq : krausTerm (LinearMap.id : L C) = (LinearMap.id : T C C) := by
    ext X x
    simp [krausTerm]
  rwa [heq] at h

/-- Domination survives an arbitrary finite entangled reference with the same
scalar constant. -/
theorem CPLe.tensor_identity_scaled {Φ Ψ : T A B} {a : ℝ}
    (h : CPLe Φ (a • Ψ)) (hΦ : IsCompletelyPositive Φ) :
    CPLe (tensorSuperoperator Φ (LinearMap.id : T C C))
      (a • tensorSuperoperator Ψ (LinearMap.id : T C C)) := by
  have hid : CPLe (LinearMap.id : T C C) LinearMap.id := by
    unfold CPLe
    rw [sub_self]
    simpa using cp_smul (cp_identity (C := C)) (c := 0) le_rfl
  have ht := h.tensor hid hΦ (cp_identity (C := C))
  have hscale : tensorSuperoperator (a • Ψ) (LinearMap.id : T C C) =
      a • tensorSuperoperator Ψ (LinearMap.id : T C C) := by
    simpa only [one_smul, mul_one] using
      tensorSuperoperator_smul Ψ (LinearMap.id : T C C) a 1
  rwa [hscale] at ht

end QuantumChannelContinuity
