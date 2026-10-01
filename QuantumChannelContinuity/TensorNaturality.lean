/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorRegrouping

/-! # Naturality of tensor channels under canonical isometries -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B C D E F G H : Type u}
  [Qudit A] [Qudit B] [Qudit C] [Qudit D] [Qudit E] [Qudit F] [Qudit G] [Qudit H]

theorem isoConj_trans (e : A ≃ₗᵢ[ℂ] B) (f : B ≃ₗᵢ[ℂ] C) :
    isoConj (e.trans f) = (isoConj f).comp (isoConj e) := by
  ext X x
  simp

theorem intertwine_trans (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (c : C ≃ₗᵢ[ℂ] E) (d : D ≃ₗᵢ[ℂ] F)
    (Φ : T A B) (Ψ : T C D) (Ω : T E F)
    (h₁ : (isoConj b).comp Φ = Ψ.comp (isoConj a))
    (h₂ : (isoConj d).comp Ψ = Ω.comp (isoConj c)) :
    (isoConj (b.trans d)).comp Φ = Ω.comp (isoConj (a.trans c)) := by
  ext1 X
  have h₁x := congrArg (fun Γ => Γ X) h₁
  have h₂x := congrArg (fun Γ => Γ (isoConj a X)) h₂
  simp only [LinearMap.comp_apply] at h₁x h₂x
  simp only [isoConj_trans, LinearMap.comp_apply, h₁x, h₂x]

/-- Tensor products preserve arbitrary superoperator intertwining identities. -/
theorem tensor_intertwine (a : A ≃ₗᵢ[ℂ] E) (b : B ≃ₗᵢ[ℂ] F)
    (c : C ≃ₗᵢ[ℂ] G) (d : D ≃ₗᵢ[ℂ] H)
    (Φ : T A B) (Φ' : T E F) (Ψ : T C D) (Ψ' : T G H)
    (hΦ : (isoConj b).comp Φ = Φ'.comp (isoConj a))
    (hΨ : (isoConj d).comp Ψ = Ψ'.comp (isoConj c)) :
    (isoConj (TensorProduct.congrIsometry b d)).comp (tensorSuperoperator Φ Ψ) =
      (tensorSuperoperator Φ' Ψ').comp (isoConj (TensorProduct.congrIsometry a c)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul,
      tensorSuperoperator_apply, isoConj_tensor]
    have hΦx := congrArg (fun Γ => Γ X) hΦ
    have hΨy := congrArg (fun Γ => Γ Y) hΨ
    simp only [LinearMap.comp_apply] at hΦx hΨy
    rw [hΦx, hΨy]
  | add x y hx hy => simp_all

@[simp] theorem isoConj_refl (X : L A) : isoConj (LinearIsometryEquiv.refl ℂ A) X = X := by
  ext x
  simp
  rfl

theorem intertwine_refl (Φ : T A B) :
    (isoConj (LinearIsometryEquiv.refl ℂ B)).comp Φ =
      Φ.comp (isoConj (LinearIsometryEquiv.refl ℂ A)) := by ext1 X; simp

theorem isoConj_assoc (X : L A) (Y : L B) (Z : L C) :
    isoConj (TensorProduct.assocIsometry ℂ A B C) (TensorProduct.map (TensorProduct.map X Y) Z) =
      TensorProduct.map X (TensorProduct.map Y Z) := by
  ext x y z
  simp [TensorProduct.map_tmul]

/-- Associativity of the tensor product of actual superoperators, transported
by the canonical Hilbert-space associators. -/
theorem tensorSuperoperator_assoc_intertwine (Φ : T A B) (Ψ : T C D) (Ω : T E F) :
    (isoConj (TensorProduct.assocIsometry ℂ B D F)).comp
        (tensorSuperoperator (tensorSuperoperator Φ Ψ) Ω) =
      (tensorSuperoperator Φ (tensorSuperoperator Ψ Ω)).comp
        (isoConj (TensorProduct.assocIsometry ℂ A C E)) := by
  ext1 Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A ⊗[ℂ] C) (ℋ₂ := E)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective X
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul X₁ X₂ =>
      simp only [LinearMap.comp_apply, l_tensor_equiv_symm_tmul,
        tensorSuperoperator_apply, isoConj_assoc]
    | add x y hx hy => simp_all [TensorProduct.add_tmul]
  | add x y hx hy => simp_all

end QuantumChannelContinuity
