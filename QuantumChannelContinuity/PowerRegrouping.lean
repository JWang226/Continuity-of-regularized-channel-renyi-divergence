/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorPowers
import QuantumChannelContinuity.TensorNaturality

/-! # Addition and multiplication of canonical channel tensor powers -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

noncomputable def unitLeftIso (A : Type) [Qudit A] :
    EuclideanSpace ℂ (Fin 1) ⊗[ℂ] A ≃ₗᵢ[ℂ] A :=
  (TensorProduct.congrIsometry tensorUnitIso (LinearIsometryEquiv.refl ℂ A)).trans
    (TensorProduct.lidIsometry ℂ A)

@[simp] theorem unitLeftIso_tmul (z : EuclideanSpace ℂ (Fin 1)) (x : A) :
    unitLeftIso A (z ⊗ₜ[ℂ] x) = tensorUnitIso z • x := by simp [unitLeftIso]

@[simp] theorem unitLeftIso_symm_apply (x : A) :
    (unitLeftIso A).symm x = tensorUnitIso.symm 1 ⊗ₜ[ℂ] x := by
  simp [unitLeftIso, TensorProduct.congrIsometry_symm]
  rfl

theorem isoConj_unitLeft_tensor (X : L (EuclideanSpace ℂ (Fin 1))) (Y : L A) :
    isoConj (unitLeftIso A) (TensorProduct.map X Y) =
      tensorUnitIso (X (tensorUnitIso.symm 1)) • Y := by
  ext x
  rw [isoConj_apply, unitLeftIso_symm_apply, TensorProduct.map_tmul, unitLeftIso_tmul]
  rfl

theorem tensor_unitLeft_intertwine (Φ : T A B) :
    (isoConj (unitLeftIso B)).comp (tensorSuperoperator (LinearMap.id : T _ _) Φ) =
      Φ.comp (isoConj (unitLeftIso A)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := EuclideanSpace ℂ (Fin 1)) (ℋ₂ := A)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      LinearMap.id_apply, isoConj_unitLeft_tensor, map_smul]
  | add x y hx hy => simp_all

/-- Concatenate the first `m` and last `n` factors. The target index uses
`n+m` so that recursion on the first factor is definitional. -/
noncomputable def powerConcatIso (A : Type) [Qudit A] [Nontrivial A] :
    (m n : ℕ) → TensorPower A m ⊗[ℂ] TensorPower A n ≃ₗᵢ[ℂ] TensorPower A (n + m)
  | 0, n => unitLeftIso (TensorPower A n)
  | m + 1, n => (TensorProduct.assocIsometry ℂ A (TensorPower A m) (TensorPower A n)).trans
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) (powerConcatIso A m n))

/-- Concatenation intertwines the actual tensor product with the actual
channel power, on every input operator. -/
theorem powerConcat_intertwine (N : CPTP A B) (m n : ℕ) :
    (isoConj (powerConcatIso B m n)).comp
        (tensorChannel (channelPower N m) (channelPower N n)).toLinearMap =
      (channelPower N (n + m)).toLinearMap.comp (isoConj (powerConcatIso A m n)) := by
  induction m with
  | zero => exact tensor_unitLeft_intertwine (channelPower N n).toLinearMap
  | succ m ih =>
    exact intertwine_trans
      (TensorProduct.assocIsometry ℂ A (TensorPower A m) (TensorPower A n))
      (TensorProduct.assocIsometry ℂ B (TensorPower B m) (TensorPower B n))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) (powerConcatIso A m n))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B) (powerConcatIso B m n))
      _ _ _
      (tensorSuperoperator_assoc_intertwine N.toLinearMap (channelPower N m).toLinearMap
        (channelPower N n).toLinearMap)
      (tensor_intertwine (LinearIsometryEquiv.refl ℂ A) (LinearIsometryEquiv.refl ℂ B)
        (powerConcatIso A m n) (powerConcatIso B m n)
        N.toLinearMap N.toLinearMap _ _ (intertwine_refl _) ih)

/-- Flatten `m` blocks each containing `n` tensor copies. -/
noncomputable def powerMulIso (A : Type) [Qudit A] [Nontrivial A] (n : ℕ) :
    (m : ℕ) → TensorPower (TensorPower A n) m ≃ₗᵢ[ℂ] TensorPower A (n * m)
  | 0 => LinearIsometryEquiv.refl ℂ _
  | m + 1 =>
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower A n))
        (powerMulIso A n m)).trans (powerConcatIso A n (n * m))

/-- Nested actual channel powers are unitarily equivalent to their flattened
power. No tensor-regrouping identity is assumed. -/
theorem powerMul_intertwine (N : CPTP A B) (n m : ℕ) :
    (isoConj (powerMulIso B n m)).comp (channelPower (channelPower N n) m).toLinearMap =
      (channelPower N (n * m)).toLinearMap.comp (isoConj (powerMulIso A n m)) := by
  induction m with
  | zero => exact intertwine_refl (identityChannel _).toLinearMap
  | succ m ih =>
    exact intertwine_trans
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower A n)) (powerMulIso A n m))
      (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ (TensorPower B n)) (powerMulIso B n m))
      (powerConcatIso A n (n * m)) (powerConcatIso B n (n * m))
      _ _ _
      (tensor_intertwine (LinearIsometryEquiv.refl ℂ (TensorPower A n))
        (LinearIsometryEquiv.refl ℂ (TensorPower B n)) (powerMulIso A n m) (powerMulIso B n m)
        (channelPower N n).toLinearMap (channelPower N n).toLinearMap _ _ (intertwine_refl _) ih)
      (powerConcat_intertwine N n (n * m))

theorem blockRenyi_power {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) (n m : ℕ) :
    blockRenyi p (channelPower N n) (channelPower M n) m = blockRenyi p N M (n * m) :=
  channelRenyi_isometry hp hp1 (powerMulIso A n m) (powerMulIso B n m)
    _ _ _ _ (powerMul_intertwine N n m) (powerMul_intertwine M n m)

theorem blockRelative_power (N M : CPTP A B) (n m : ℕ) :
    blockRelative (channelPower N n) (channelPower M n) m = blockRelative N M (n * m) :=
  channelRelative_isometry (powerMulIso A n m) (powerMulIso B n m)
    _ _ _ _ (powerMul_intertwine N n m) (powerMul_intertwine M n m)

end QuantumChannelContinuity
