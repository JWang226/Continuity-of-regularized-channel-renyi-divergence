/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.SDPTrace
import Mathlib.Topology.Sequences

/-!
# The closed semidefinite slack cone and exact separation

Closedness, including attainment at the boundary, follows from the trace bound
on a positive slack operator. Hahn–Banach separation then supplies positive
operator witnesses satisfying the dual semidefinite constraints.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

universe u
variable {H K : Type u} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Primal semidefinite slack cone for a trace-preserving linear map. -/
noncomputable def sdpSlackCone (τ : Hermitian H →ₗ[ℝ] Hermitian K) :
    PointedCone ℝ (Hermitian H × Hermitian K) where
  carrier := {p | ∃ Q : Hermitian H, 0 ≤ Q ∧ p.1 ≤ Q ∧ τ Q ≤ p.2}
  zero_mem' := ⟨0, le_rfl, le_rfl, by simp⟩
  add_mem' := by
    rintro x y ⟨Q,hQ,hx,hτQ⟩ ⟨R,hR,hy,hτR⟩
    exact ⟨Q+R, add_nonneg hQ hR, add_le_add hx hy, by simpa using add_le_add hτQ hτR⟩
  smul_mem' := by
    rintro r p ⟨Q,hQ,hp,hτQ⟩
    refine ⟨(r : ℝ) • Q, hermitian_smul_nonneg r.property hQ,
      hermitian_smul_mono r.property hp, ?_⟩
    simpa using hermitian_smul_mono r.property hτQ

/-- The slack cone is closed: positive slacks in a convergent feasible sequence
have bounded trace, hence bounded norm and a convergent subsequence. -/
theorem sdpSlackCone_isClosed (τ : Hermitian H →ₗ[ℝ] Hermitian K)
    (htrace : ∀ Q, hermitianTrace (H := K) (τ Q) = hermitianTrace (H := H) Q) :
    IsClosed (sdpSlackCone τ : Set (Hermitian H × Hermitian K)) := by
  apply IsSeqClosed.isClosed
  intro p z hp hz
  choose Q hQ hx hτ using hp
  have htr : Tendsto (fun n => hermitianTrace (H := K) (p n).2) atTop
      (𝓝 (hermitianTrace (H := K) z.2)) :=
    (hermitianTrace (H := K)).continuous_of_finiteDimensional.tendsto _ |>.comp ((continuous_snd.tendsto z).comp hz)
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto _ htr).bddAbove
  have hbound (n) : ‖Q n‖ ≤ C := by
    calc
      ‖Q n‖ ≤ hermitianTrace (H := H) (Q n) := hermitian_norm_le_trace (hQ n)
      _ = hermitianTrace (H := K) (τ (Q n)) := (htrace _).symm
      _ ≤ hermitianTrace (H := K) (p n).2 := hermitianTrace_mono (hτ n)
      _ ≤ C := hC (Set.mem_range_self n)
  obtain ⟨q,_,φ,hφ,hq⟩ := (isCompact_closedBall (0 : Hermitian H) C).tendsto_subseq
    (fun n => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound n)
  have hpφ := hz.comp hφ.tendsto_atTop
  refine ⟨q, ?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hq (fun n => hQ (φ n))
  · exact le_of_tendsto_of_tendsto' ((continuous_fst.tendsto z).comp hpφ) hq (fun n => hx (φ n))
  · exact le_of_tendsto_of_tendsto'
      (τ.continuous_of_finiteDimensional.tendsto _ |>.comp hq) ((continuous_snd.tendsto z).comp hpφ) (fun n => hτ (φ n))

/-- Trace symmetry on Hermitian operators. -/
theorem hermitianTracePair_symm (X Y : Hermitian H) :
    hermitianTracePair (H := H) X Y = hermitianTracePair (H := H) Y X := by
  change (Tr ((X : L H) ∘ₗ (Y : L H))).re = (Tr ((Y : L H) ∘ₗ (X : L H))).re
  rw [LinearMap.trace_comp_comm']

/-- Exact primal/dual separation for the semidefinite slack problem. This is
a proved finite-dimensional conic duality statement, with no Slater premise. -/
theorem sdpSlack_separation
    (τ : Hermitian H →ₗ[ℝ] Hermitian K) (σ : Hermitian K →ₗ[ℝ] Hermitian H)
    (htrace : ∀ Q, hermitianTrace (H := K) (τ Q) = hermitianTrace (H := H) Q)
    (hadj : ∀ Q Y, hermitianTracePair (H := K) Y (τ Q) =
      hermitianTracePair (H := H) (σ Y) Q)
    (D : Hermitian H) (Z : Hermitian K)
    (hno : ¬ ∃ Q : Hermitian H, 0 ≤ Q ∧ D ≤ Q ∧ τ Q ≤ Z) :
    ∃ W : Hermitian H, ∃ Y : Hermitian K,
      0 ≤ W ∧ 0 ≤ Y ∧ W ≤ σ Y ∧
      hermitianTracePair (H := K) Y Z < hermitianTracePair (H := H) W D := by
  let cone : ProperCone ℝ (Hermitian H × Hermitian K) :=
    ⟨sdpSlackCone τ, sdpSlackCone_isClosed τ htrace⟩
  obtain ⟨f,hf,hneg⟩ := cone.hyperplane_separation_point (x₀ := (D,Z)) hno
  let f₁ := f.toLinearMap.comp (LinearMap.inl ℝ (Hermitian H) (Hermitian K))
  let f₂ := f.toLinearMap.comp (LinearMap.inr ℝ (Hermitian H) (Hermitian K))
  obtain ⟨X,hX⟩ := hermitianTracePair_surjective (H := H) f₁
  obtain ⟨Y,hY⟩ := hermitianTracePair_surjective (H := K) f₂
  have heval (x : Hermitian H) (y : Hermitian K) :
      f (x,y) = hermitianTracePair (H := H) X x + hermitianTracePair (H := K) Y y := by
    rw [hX,hY]
    simpa only [f₁,f₂,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,
      Prod.mk_add_mk,add_zero,zero_add] using (map_add f (x,0) (0,y))
  have hW : 0 ≤ -X := by
    apply (hermitian_nonneg_iff_trace (-X)).mpr
    intro P hP
    have hm : (-P,0) ∈ cone := ⟨0,le_rfl,neg_nonpos.mpr hP,by simp⟩
    have h := hf (-P,0) hm
    simpa only [heval, map_zero, add_zero, map_neg, LinearMap.neg_apply] using h
  have hYn : 0 ≤ Y := by
    apply (hermitian_nonneg_iff_trace Y).mpr
    intro P hP
    have hm : (0,P) ∈ cone := ⟨0,le_rfl,le_rfl,by simpa using hP⟩
    simpa only [heval,map_zero,zero_add] using hf (0,P) hm
  have hle : -X ≤ σ Y := by
    apply sub_nonneg.mp
    apply (hermitian_nonneg_iff_trace (σ Y - -X)).mpr
    intro P hP
    have hm : (P,τ P) ∈ cone := ⟨P,hP,le_rfl,le_rfl⟩
    have h := hf (P,τ P) hm
    rw [heval,hadj] at h
    simpa only [sub_neg_eq_add,map_add,LinearMap.add_apply,add_comm] using h
  refine ⟨-X,Y,hW,hYn,hle,?_⟩
  rw [heval] at hneg
  simp only [map_neg,LinearMap.neg_apply]
  linarith

end QuantumChannelContinuity
