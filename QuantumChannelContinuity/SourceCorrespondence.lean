/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorPowers

/-!
# Correspondence with the manuscript's tensor-factor convention

The manuscript writes stabilized outputs as `(id ⊗ N)(|ψ⟩⟨ψ|)`, with the
reference first. The implementation's `amplifiedOutput` acts on the first
factor. Tensor swaps identify the two output states and their optimized
support-aware divergences at every admissible Rényi order.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B]

/-- Conjugating by the tensor swap exchanges tensor-product operators. -/
theorem isoConj_comm_tensor (X : L A) (Y : L B) :
    isoConj (TensorProduct.commIsometry ℂ A B) (TensorProduct.map X Y) =
      TensorProduct.map Y X := by
  change (TensorProduct.commIsometry ℂ A B).toLinearMap.comp
    ((TensorProduct.map X Y).comp
      (LinearMap.adjoint (TensorProduct.commIsometry ℂ A B).toLinearMap)) = _
  rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
  ext a b
  simp

/-- The tensor swap intertwines the actual reference-first superoperator with
`amplifyWithId` on every input operator. -/
theorem tensorSuperoperator_id_swap (N : CPTP A B) (X : L (A ⊗[ℂ] A)) :
    tensorSuperoperator (LinearMap.id : T A A) N.toLinearMap
      (isoConj (TensorProduct.commIsometry ℂ A A) X) =
    isoConj (TensorProduct.commIsometry ℂ B A) (amplifyWithId N.toLinearMap X) := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := A)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, isoConj_comm_tensor, tensorSuperoperator_apply,
      amplifyWithId_tensor, isoConj_comm_tensor]
    rfl
  | add x y hx hy => simp_all

variable [Nontrivial A] [Nontrivial B]

/-- The manuscript's reference-first output state: the identity acts on the
reference copy of the input, and the supplied channel acts on the second factor. -/
noncomputable def referenceFirstOutput (N : CPTP A B)
    (ρ : DensityState (A ⊗[ℂ] A)) : DensityState (A ⊗[ℂ] B) :=
  ρ.map (tensorChannel (identityChannel A) N)

/-- Swapping input and output factors intertwines the two actual channel actions
on arbitrary density operators, including entangled inputs. -/
theorem referenceFirstOutput_swap (N : CPTP A B)
    (ρ : DensityState (A ⊗[ℂ] A)) :
    referenceFirstOutput N
      (ρ.map (isometryChannel (TensorProduct.commIsometry ℂ A A))) =
    (amplifiedOutput N ρ).map
      (isometryChannel (TensorProduct.commIsometry ℂ B A)) := by
  apply DensityState.ext
  exact tensorSuperoperator_id_swap N ρ.op

/-- Isometric transport is a bijection on the full normalized pure-input domain. -/
noncomputable def pureInputEquiv (e : A ≃ₗᵢ[ℂ] B) : PureInput A ≃ PureInput B where
  toFun ψ := ψ.mapIso e
  invFun ψ := ψ.mapIso e.symm
  left_inv ψ := by
    cases ψ
    simp [PureInput.mapIso]
  right_inv ψ := by
    cases ψ
    simp [PureInput.mapIso]

/-- The implementation's channel Rényi divergence equals the manuscript's
reference-first pure-input supremum, with the same reference dimension. -/
theorem channelRenyi_eq_referenceFirst {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) :
    channelRenyi p N M =
      ⨆ ψ : PureInput (A ⊗[ℂ] A),
        (stateRenyi p (referenceFirstOutput N ψ.density)
          (referenceFirstOutput M ψ.density)).toENNReal := by
  rw [← (pureInputEquiv (TensorProduct.commIsometry ℂ A A)).iSup_comp]
  apply iSup_congr
  intro ψ
  change (stateRenyi p (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density)).toENNReal =
      (stateRenyi p (referenceFirstOutput N (ψ.mapIso
        (TensorProduct.commIsometry ℂ A A)).density)
        (referenceFirstOutput M (ψ.mapIso
          (TensorProduct.commIsometry ℂ A A)).density)).toENNReal
  rw [PureInput.density_mapIso, referenceFirstOutput_swap, referenceFirstOutput_swap,
    stateRenyi_isometry hp hp1]

/-- Relative entropy has the same exact correspondence of pure-input suprema,
including support-mismatch infinities. -/
theorem channelRelative_eq_referenceFirst (N M : CPTP A B) :
    channelRelative N M =
      ⨆ ψ : PureInput (A ⊗[ℂ] A),
        (stateRelative (referenceFirstOutput N ψ.density)
          (referenceFirstOutput M ψ.density)).toENNReal := by
  rw [← (pureInputEquiv (TensorProduct.commIsometry ℂ A A)).iSup_comp]
  apply iSup_congr
  intro ψ
  change (stateRelative (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density)).toENNReal =
      (stateRelative (referenceFirstOutput N (ψ.mapIso
        (TensorProduct.commIsometry ℂ A A)).density)
        (referenceFirstOutput M (ψ.mapIso
          (TensorProduct.commIsometry ℂ A A)).density)).toENNReal
  rw [PureInput.density_mapIso, referenceFirstOutput_swap, referenceFirstOutput_swap,
    stateRelative_isometry]

end QuantumChannelContinuity
