/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorWords

/-! # Isometric invariance and regrouping of concrete quantum channels -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

/-- Conjugation by an isometric equivalence of Hilbert spaces. -/
noncomputable def isoConj (e : A ≃ₗᵢ[ℂ] B) : T A B := krausTerm e.toLinearMap

@[simp] theorem isoConj_apply (e : A ≃ₗᵢ[ℂ] B) (X : L A) (b : B) :
    isoConj e X b = e (X (e.symm b)) := by
  simp [isoConj, krausTerm, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

@[simp] theorem isoConj_symm (e : A ≃ₗᵢ[ℂ] B) (X : L A) :
    isoConj e.symm (isoConj e X) = X := by ext x; simp

@[simp] theorem isoConj_apply_symm (e : A ≃ₗᵢ[ℂ] B) (X : L B) :
    isoConj e (isoConj e.symm X) = X := by ext x; simp

@[simp] theorem isoConj_outer (e : A ≃ₗᵢ[ℂ] B) (x y : A) :
    isoConj e (outer_product x y) = outer_product (e x) (e y) := by
  exact comp_outer_product_adjoint e.toLinearMap x y

/-- A change of Hilbert-space coordinates is an actual CPTP map. -/
noncomputable def isometryChannel (e : A ≃ₗᵢ[ℂ] B) : CPTP A B where
  toFun := isoConj e
  map_add' := (isoConj e).map_add
  map_smul' := (isoConj e).map_smul
  map_cstarMatrix_nonneg' :=
    (isCompletelyPositive_iff_cstarMatrix_nonneg _).1 (krausTerm_isCompletelyPositive e.toLinearMap)
  trace_map X := by
    change Tr X = Tr (e.toLinearMap ∘ₗ X ∘ₗ e.toLinearMap.adjoint)
    rw [LinearMap.trace_comp_comm']
    congr 1
    ext x
    simp [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

@[simp] theorem DensityState.map_isometry_symm [Nontrivial A] [Nontrivial B] (e : A ≃ₗᵢ[ℂ] B) (ρ : DensityState A) :
    (ρ.map (isometryChannel e)).map (isometryChannel e.symm) = ρ := by
  apply DensityState.ext
  exact isoConj_symm e ρ.op

/-- Support-aware divergence is unchanged by isometric changes of coordinates. -/
theorem stateRenyi_isometry [Nontrivial A] [Nontrivial B]
    {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (e : A ≃ₗᵢ[ℂ] B) (ρ σ : DensityState A) :
    stateRenyi p (ρ.map (isometryChannel e)) (σ.map (isometryChannel e)) =
      stateRenyi p ρ σ := by
  apply le_antisymm (stateRenyi_dataProcessing (isometryChannel e) hp hp1 ρ σ)
  have h := stateRenyi_dataProcessing (isometryChannel e.symm) hp hp1
    (ρ.map (isometryChannel e)) (σ.map (isometryChannel e))
  simpa using h

theorem stateRelative_isometry [Nontrivial A] [Nontrivial B]
    (e : A ≃ₗᵢ[ℂ] B) (ρ σ : DensityState A) :
    stateRelative (ρ.map (isometryChannel e)) (σ.map (isometryChannel e)) =
      stateRelative ρ σ := by
  apply le_antisymm (stateRelative_dataProcessing (isometryChannel e) ρ σ)
  have h := stateRelative_dataProcessing (isometryChannel e.symm)
    (ρ.map (isometryChannel e)) (σ.map (isometryChannel e))
  simpa using h

/-- Conjugation respects tensor products of operators. -/
theorem isoConj_tensor (e : A ≃ₗᵢ[ℂ] B) (f : C ≃ₗᵢ[ℂ] D) (X : L A) (Y : L C) :
    isoConj (TensorProduct.congrIsometry e f) (TensorProduct.map X Y) =
      TensorProduct.map (isoConj e X) (isoConj f Y) := by
  have heq : (TensorProduct.congrIsometry e f).toLinearMap =
      TensorProduct.map e.toLinearMap f.toLinearMap := by ext x y; rfl
  simp only [isoConj, heq]
  exact tensor_kraus_apply _ _ X Y

/-- The stabilized outputs intertwine under changes of input/output coordinates. -/
theorem amplify_intertwine (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N : CPTP A B) (N' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (X : L (A ⊗[ℂ] A)) :
    isoConj (TensorProduct.congrIsometry b a) (amplifyWithId N.toLinearMap X) =
      amplifyWithId N'.toLinearMap (isoConj (TensorProduct.congrIsometry a a) X) := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := A)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, amplifyWithId_tensor, isoConj_tensor,
      isoConj_tensor, amplifyWithId_tensor]
    have h := congrArg (fun Φ : T A D => Φ X) hN
    simpa only [LinearMap.comp_apply] using congrArg (fun Z => TensorProduct.map Z (isoConj a Y)) h
  | add x y hx hy => simp_all

/-- A normalized pure input transported through an isometric equivalence. -/
noncomputable def PureInput.mapIso (e : A ≃ₗᵢ[ℂ] B) (ψ : PureInput A) : PureInput B :=
  ⟨e ψ.vector, by simpa using ψ.norm_one⟩

@[simp] theorem PureInput.density_mapIso [Nontrivial A] [Nontrivial B] (e : A ≃ₗᵢ[ℂ] B) (ψ : PureInput A) :
    (ψ.mapIso e).density = ψ.density.map (isometryChannel e) := by
  apply DensityState.ext
  exact (isoConj_outer e ψ.vector ψ.vector).symm

/-- Coordinate changes commute with the actual amplified output states. -/
theorem amplifiedOutput_mapIso [Nontrivial A] [Nontrivial B]
    [Nontrivial C] [Nontrivial D] (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N : CPTP A B) (N' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (ψ : PureInput (A ⊗[ℂ] A)) :
    amplifiedOutput N' (ψ.mapIso (TensorProduct.congrIsometry a a)).density =
      (amplifiedOutput N ψ.density).map (isometryChannel (TensorProduct.congrIsometry b a)) := by
  apply DensityState.ext
  rw [PureInput.density_mapIso]
  exact (amplify_intertwine a b N N' hN ψ.density.op).symm

/-- Inverting an intertwining relation for invertible quantum coordinates. -/
theorem intertwine_symm (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (Φ : T A B) (Ψ : T C D)
    (h : (isoConj b).comp Φ = Ψ.comp (isoConj a)) :
    (isoConj b.symm).comp Ψ = Φ.comp (isoConj a.symm) := by
  ext1 X
  have hh := congrArg (fun Γ : T A D => Γ (isoConj a.symm X)) h
  have hh' := congrArg (isoConj b.symm) hh
  simpa only [LinearMap.comp_apply, isoConj_symm, isoConj_apply_symm, LinearIsometryEquiv.symm_symm] using hh'.symm

theorem channelRenyi_le_of_intertwine [Nontrivial A] [Nontrivial B]
    [Nontrivial C] [Nontrivial D] {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N M : CPTP A B) (N' M' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (hM : (isoConj b).comp M.toLinearMap = M'.toLinearMap.comp (isoConj a)) :
    channelRenyi p N M ≤ channelRenyi p N' M' := by
  apply iSup_le
  intro ψ
  have h := stateRenyi_le_channel N' M' p (ψ.mapIso (TensorProduct.congrIsometry a a))
  rw [amplifiedOutput_mapIso a b N N' hN, amplifiedOutput_mapIso a b M M' hM,
    stateRenyi_isometry hp hp1] at h
  exact h

/-- Stabilized channel Rényi divergence is unchanged under input/output
isometric equivalences, including singular states and infinite values. -/
theorem channelRenyi_isometry [Nontrivial A] [Nontrivial B]
    [Nontrivial C] [Nontrivial D] {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N M : CPTP A B) (N' M' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (hM : (isoConj b).comp M.toLinearMap = M'.toLinearMap.comp (isoConj a)) :
    channelRenyi p N M = channelRenyi p N' M' :=
  le_antisymm (channelRenyi_le_of_intertwine hp hp1 a b N M N' M' hN hM)
    (channelRenyi_le_of_intertwine hp hp1 a.symm b.symm N' M' N M
      (intertwine_symm a b _ _ hN) (intertwine_symm a b _ _ hM))

theorem channelRelative_le_of_intertwine [Nontrivial A] [Nontrivial B]
    [Nontrivial C] [Nontrivial D]
    (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N M : CPTP A B) (N' M' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (hM : (isoConj b).comp M.toLinearMap = M'.toLinearMap.comp (isoConj a)) :
    channelRelative N M ≤ channelRelative N' M' := by
  apply iSup_le
  intro ψ
  have h := stateRelative_le_channel N' M' (ψ.mapIso (TensorProduct.congrIsometry a a))
  rw [amplifiedOutput_mapIso a b N N' hN, amplifiedOutput_mapIso a b M M' hM,
    stateRelative_isometry] at h
  exact h

theorem channelRelative_isometry [Nontrivial A] [Nontrivial B]
    [Nontrivial C] [Nontrivial D]
    (a : A ≃ₗᵢ[ℂ] C) (b : B ≃ₗᵢ[ℂ] D)
    (N M : CPTP A B) (N' M' : CPTP C D)
    (hN : (isoConj b).comp N.toLinearMap = N'.toLinearMap.comp (isoConj a))
    (hM : (isoConj b).comp M.toLinearMap = M'.toLinearMap.comp (isoConj a)) :
    channelRelative N M = channelRelative N' M' :=
  le_antisymm (channelRelative_le_of_intertwine a b N M N' M' hN hM)
    (channelRelative_le_of_intertwine a.symm b.symm N' M' N M
      (intertwine_symm a b _ _ hN) (intertwine_symm a b _ _ hM))

end QuantumChannelContinuity
