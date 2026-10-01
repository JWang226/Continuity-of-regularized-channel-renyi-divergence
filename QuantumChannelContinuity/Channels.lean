/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.Foundations

/-!
# Concrete stabilized divergences and hockey-stick testing

Reference systems, pure inputs, channel outputs, and tests are actual
finite-dimensional quantum objects from Lean-Quantum. The reference is a
second copy of the input space, as in the manuscript.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

universe u

variable {H K : Type u} [Qudit H] [Qudit K]

/-- A normalized pure input vector. -/
structure PureInput (H : Type u) [Qudit H] where
  vector : H
  norm_one : ‖vector‖ = 1

noncomputable instance [Nontrivial H] : Nonempty (PureInput H) := by
  let b := stdOrthonormalBasis ℂ H
  let i : Fin (Module.finrank ℂ H) := ⟨0, Module.finrank_pos⟩
  exact ⟨⟨b i, b.norm_eq_one i⟩⟩

/-- The rank-one density operator of a pure input. -/
noncomputable def PureInput.density (ψ : PureInput H) : DensityState H where
  op := outer_product ψ.vector ψ.vector
  nonneg := outer_product_self_nonneg _
  trace_one := by
    rw [trace_outer_product, inner_self_eq_norm_sq_to_K, ψ.norm_one]
    norm_num

/-- Amplification acts as the channel on the first tensor factor. -/
theorem amplifyWithId_tensor (E : CPTP H K) (A B : L H) :
    amplifyWithId E.toLinearMap (TensorProduct.map A B) =
      TensorProduct.map (E.toFun A) B := by
  rw [← l_tensor_equiv_symm_tmul, ← l_tensor_equiv_symm_tmul]
  simp [amplifyWithId]

/-- The actual amplification preserves trace on arbitrary, possibly entangled,
operators. The proof extends from simple tensors by linearity. -/
theorem trace_amplifyWithId (E : CPTP H K) (ρ : L (H ⊗[ℂ] H)) :
    Tr (amplifyWithId E.toLinearMap ρ) = Tr ρ := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := H) (ℋ₂ := H)).symm.surjective ρ
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul A B =>
      rw [l_tensor_equiv_symm_tmul, amplifyWithId_tensor,
        LinearMap.trace_tensorProduct', LinearMap.trace_tensorProduct', ← E.trace_map]
  | add x y hx hy => simp_all

/-- A stabilized output is a normalized positive density operator. -/
noncomputable def amplifiedOutput (E : CPTP H K)
    (ρ : DensityState (H ⊗[ℂ] H)) : DensityState (K ⊗[ℂ] H) where
  op := amplifyWithId E.toLinearMap ρ.op
  nonneg := cp_to_tensor E.toLinearMap ⟨E.toCompletelyPositiveMap, rfl⟩ ρ.op ρ.nonneg
  trace_one := (trace_amplifyWithId E ρ.op).trans ρ.trace_one

instance tensorQuditNontrivial [Nontrivial H] [Nontrivial K] :
    Nontrivial (H ⊗[ℂ] K) :=
  (Module.finrank_pos_iff (R := ℂ)).mp (by
    rw [Module.finrank_tensorProduct (R := ℂ) (S := ℂ) (M := H) (M' := K)]
    exact Nat.mul_pos (Module.finrank_pos (R := ℂ) (M := H))
      (Module.finrank_pos (R := ℂ) (M := K)))

variable [Nontrivial H] [Nontrivial K]

/-- Stabilized sandwiched Rényi divergence, optimized over pure entangled
inputs with a reference copy of the input space. -/
noncomputable def channelRenyi (α : ℝ) (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ ψ : PureInput (H ⊗[ℂ] H),
    (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal

/-- Stabilized channel relative entropy using the same pure-input domain. -/
noncomputable def channelRelative (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ ψ : PureInput (H ⊗[ℂ] H),
    (stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal

/-- Every tested input is bounded by the concrete stabilized divergence. -/
theorem stateRenyi_le_channel (N M : CPTP H K) (α : ℝ)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal ≤
      channelRenyi α N M := by
  unfold channelRenyi
  exact le_iSup (fun φ : PureInput (H ⊗[ℂ] H) =>
    (stateRenyi α (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)).toENNReal) ψ

theorem stateRelative_le_channel (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    (stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal ≤
      channelRelative N M := by
  unfold channelRelative
  exact le_iSup (fun φ : PureInput (H ⊗[ℂ] H) =>
    (stateRelative (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)).toENNReal) ψ

/-- An upper bound on the concrete channel supremum bounds every input in
the support-aware extended-real convention. -/
theorem stateRenyi_le_of_channel_le (N M : CPTP H K) {α a : ℝ}
    (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1) (ha : 0 ≤ a)
    (hD : channelRenyi α N M ≤ ENNReal.ofReal a)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density) ≤ (a : EReal) := by
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    ((stateRenyi_le_channel N M α ψ).trans hD)
  rw [EReal.coe_toENNReal (stateRenyi_nonneg hα hα1 _ _), EReal.coe_ennreal_ofReal,
    max_eq_left ha] at h
  exact h

theorem stateRelative_le_of_channel_le (N M : CPTP H K) {a : ℝ}
    (ha : 0 ≤ a) (hD : channelRelative N M ≤ ENNReal.ofReal a)
    (ψ : PureInput (H ⊗[ℂ] H)) :
    stateRelative (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density) ≤ (a : EReal) := by
  have h := EReal.coe_ennreal_le_coe_ennreal_iff.mpr
    ((stateRelative_le_channel N M ψ).trans hD)
  rw [EReal.coe_toENNReal (stateRelative_nonneg _ _), EReal.coe_ennreal_ofReal,
    max_eq_left ha] at h
  exact h

/-- A genuine support-mismatched stabilized output forces infinite channel
relative entropy. No abstract infinity witness is assumed for this implication. -/
theorem channelRelative_top_of_support_mismatch (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H))
    (hs : ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op) :
    channelRelative N M = ⊤ := by
  apply top_unique
  have h := stateRelative_le_channel N M ψ
  simpa [stateRelative_eq_top_of_not_support _ _ hs] using h

/-- The same concrete input gives infinity for every order above one. -/
theorem channelRenyi_top_of_support_mismatch (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H)) {α : ℝ} (hα : 1 < α)
    (hs : ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op) :
    channelRenyi α N M = ⊤ := by
  apply top_unique
  have h := stateRenyi_le_channel N M α ψ
  simpa [stateRenyi_eq_top_of_not_support hα _ _ hs] using h

end QuantumChannelContinuity
