/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.Channels

/-!
# Tensor products and positive tensor powers of concrete channels

Complete positivity is proved using tensor products of Kraus operators;
trace preservation is extended from simple tensors by linearity.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

/-- The tensor product of two superoperators, transported through the
canonical finite-dimensional operator tensor equivalence. -/
noncomputable def tensorSuperoperator (Φ : T A B) (Ψ : T C D) :
    T (A ⊗[ℂ] C) (B ⊗[ℂ] D) :=
  (l_tensor_equiv (ℋ₁ := B) (ℋ₂ := D)).symm.toLinearMap.comp
    ((TensorProduct.map Φ Ψ).comp (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).toLinearMap)

theorem tensorSuperoperator_apply (Φ : T A B) (Ψ : T C D) (X : L A) (Y : L C) :
    tensorSuperoperator Φ Ψ (TensorProduct.map X Y) = TensorProduct.map (Φ X) (Ψ Y) := by
  rw [← l_tensor_equiv_symm_tmul, ← l_tensor_equiv_symm_tmul]
  simp [tensorSuperoperator]

/-- Tensoring two Kraus operators tensors their conjugation maps. -/
theorem tensor_kraus_apply (V : A →ₗ[ℂ] B) (W : C →ₗ[ℂ] D) (X : L A) (Y : L C) :
    krausTerm (TensorProduct.map V W) (TensorProduct.map X Y) =
      TensorProduct.map (krausTerm V X) (krausTerm W Y) := by
  simp [krausTerm, TensorProduct.adjoint_map, ← TensorProduct.map_comp]

/-- The tensor product of actual completely positive superoperators is
completely positive, including every amplification. -/
theorem tensorSuperoperator_cp (Φ : T A B) (Ψ : T C D)
    (hΦ : IsCompletelyPositive Φ) (hΨ : IsCompletelyPositive Ψ) :
    IsCompletelyPositive (tensorSuperoperator Φ Ψ) := by
  classical
  obtain ⟨ι, hi, fi, V, hV⟩ := cp_to_kraus (stdOrthonormalBasis ℂ A).toBasis Φ hΦ
  obtain ⟨κ, hk, fk, W, hW⟩ := cp_to_kraus (stdOrthonormalBasis ℂ C).toBasis Ψ hΨ
  letI := hi
  letI := fi
  letI := hk
  letI := fk
  have heq : tensorSuperoperator Φ Ψ =
      ∑ i : ι × κ, krausTerm (TensorProduct.map (V i.1) (W i.2)) := by
    apply LinearMap.ext
    intro Z
    obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul X Y =>
      rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply, hV, hW]
      rw [LinearMap.sum_apply, Fintype.sum_prod_type]
      simp only [tensor_kraus_apply]
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
        simp [TensorProduct.sum_tmul, TensorProduct.tmul_sum, krausTerm]
        exact Finset.sum_comm
      | add x y hx hy => simp_all [map_add]
    | add x y hx hy => simp_all [Finset.sum_add_distrib]
  rw [heq]
  exact sum_krausTerm_isCompletelyPositive _

/-- Trace preservation of the tensor product. -/
theorem tensorSuperoperator_trace (Φ : CPTP A B) (Ψ : CPTP C D)
    (Z : L (A ⊗[ℂ] C)) :
    Tr (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap Z) = Tr Z := by
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct']
    change Tr (Φ.toFun X) * Tr (Ψ.toFun Y) = Tr X * Tr Y
    rw [← Φ.trace_map, ← Ψ.trace_map]
  | add x y hx hy => simp_all

/-- Tensor product of concrete CPTP quantum channels. -/
noncomputable def tensorChannel (Φ : CPTP A B) (Ψ : CPTP C D) :
    CPTP (A ⊗[ℂ] C) (B ⊗[ℂ] D) where
  toFun := tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap
  map_add' := (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap).map_add
  map_smul' := (tensorSuperoperator Φ.toLinearMap Ψ.toLinearMap).map_smul
  map_cstarMatrix_nonneg' k X hX := by
    obtain ⟨Γ, hΓ⟩ := tensorSuperoperator_cp Φ.toLinearMap Ψ.toLinearMap
      ⟨Φ.toCompletelyPositiveMap, rfl⟩ ⟨Ψ.toCompletelyPositiveMap, rfl⟩
    have h := Γ.map_cstarMatrix_nonneg' k X hX
    rw [hΓ] at h
    exact h
  trace_map X := (tensorSuperoperator_trace Φ Ψ X).symm

end QuantumChannelContinuity
