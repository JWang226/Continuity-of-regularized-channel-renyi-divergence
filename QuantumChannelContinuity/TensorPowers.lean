/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorRegrouping

/-! # Canonical regrouping of concrete channel tensor powers -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The canonical scalar coordinate on the one-dimensional tensor unit. -/
noncomputable def tensorUnitIso : EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℂ] ℂ :=
  (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

noncomputable def powerOneIso (A : Type) [Qudit A] [Nontrivial A] :
    TensorPower A 1 ≃ₗᵢ[ℂ] A :=
  (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ A) tensorUnitIso).trans
    ((TensorProduct.commIsometry ℂ A ℂ).trans (TensorProduct.lidIsometry ℂ A))

@[simp] theorem powerOneIso_tmul (x : A) (z : EuclideanSpace ℂ (Fin 1)) :
    powerOneIso A (x ⊗ₜ[ℂ] z) = tensorUnitIso z • x := by
  simp [powerOneIso, TensorPower, tensorPowerSpace]

@[simp] theorem powerOneIso_symm_apply (x : A) :
    (powerOneIso A).symm x = x ⊗ₜ[ℂ] tensorUnitIso.symm 1 := by
  simp [powerOneIso, TensorPower, tensorPowerSpace, TensorProduct.congrIsometry_symm]
  rfl

/-- Conjugating an operator with a scalar factor into a one-copy space. -/
theorem isoConj_powerOne_tensor (X : L A) (Y : L (EuclideanSpace ℂ (Fin 1))) :
    isoConj (powerOneIso A) (TensorProduct.map X Y) =
      tensorUnitIso (Y (tensorUnitIso.symm 1)) • X := by
  ext x
  rw [isoConj_apply, powerOneIso_symm_apply]
  calc
    _ = powerOneIso A (X x ⊗ₜ[ℂ] Y (tensorUnitIso.symm 1)) :=
      congrArg (powerOneIso A) (TensorProduct.map_tmul X Y x (tensorUnitIso.symm 1))
    _ = _ := powerOneIso_tmul _ _

/-- A single canonical channel copy differs only by the tensor-unit coordinates. -/
theorem channelPower_one_intertwine (N : CPTP A B) :
    (isoConj (powerOneIso B)).comp (channelPower N 1).toLinearMap =
      N.toLinearMap.comp (isoConj (powerOneIso A)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A)
    (ℋ₂ := EuclideanSpace ℂ (Fin 1))).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    change isoConj (powerOneIso B)
      (tensorSuperoperator N.toLinearMap (LinearMap.id : T _ _)
        ((l_tensor_equiv (ℋ₁ := A) (ℋ₂ := EuclideanSpace ℂ (Fin 1))).symm (X ⊗ₜ[ℂ] Y))) = _
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply]
    change isoConj (powerOneIso B) (TensorProduct.map (N.toLinearMap X) Y) =
      N.toLinearMap (isoConj (powerOneIso A) (TensorProduct.map X Y))
    rw [isoConj_powerOne_tensor, isoConj_powerOne_tensor, map_smul]
  | add x y hx hy => simp_all

/-- Block length one equals the original stabilized channel divergence. -/
theorem blockRenyi_one {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1) (N M : CPTP A B) :
    blockRenyi p N M 1 = channelRenyi p N M :=
  channelRenyi_isometry hp hp1 (powerOneIso A) (powerOneIso B)
    (channelPower N 1) (channelPower M 1) N M
    (channelPower_one_intertwine N) (channelPower_one_intertwine M)

theorem blockRelative_one (N M : CPTP A B) :
    blockRelative N M 1 = channelRelative N M :=
  channelRelative_isometry (powerOneIso A) (powerOneIso B)
    (channelPower N 1) (channelPower M 1) N M
    (channelPower_one_intertwine N) (channelPower_one_intertwine M)

end QuantumChannelContinuity
