/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.Channels
import QuantumChannelContinuity.TensorOrder

/-!
# Choi support, finite channel domination, and a concrete infinite witness

The normalized vectorization of the identity is an actual pure input. Its
outputs are positive scalar multiples of the Choi operators. Thus support
inclusion yields a finite completely-positive domination constant, and its
failure supplies the explicit state witness used by the infinite branch.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u
variable {A B : Type u} [Qudit A] [Qudit B]

/-- The Choi construction is linear in the superoperator. -/
noncomputable def choiLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : T A B →ₗ[ℂ] L (B ⊗[ℂ] A) where
  toFun := choi b
  map_add' Φ Ψ := by
    simp only [choi, TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.add_apply]
  map_smul' c Φ := by
    simp only [choi, TensorProduct.map_smul_left, LinearMap.smul_comp,
      LinearMap.comp_smul, LinearMap.smul_apply, RingHom.id_apply]

@[simp] theorem choiLinear_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (Φ : T A B) : choiLinear b Φ = choi b Φ := rfl

/-- Every operator on the output/reference tensor product has a unique
superoperator as its Choi preimage. -/
theorem choiLinear_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) : Function.Surjective (choiLinear (B := B) b) := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (choi_injective b)
  simp only [T, L, Module.finrank_linearMap, Module.finrank_tensorProduct]
  ring

/-- Complete-positive order is exactly ordinary order of Choi operators. -/
theorem cpLe_iff_choi_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ A) (Φ Ψ : T A B) :
    CPLe Φ Ψ ↔ choi b Φ ≤ choi b Ψ := by
  rw [CPLe, cp_iff_choi b, ChoiPositive]
  change 0 ≤ choiLinear b (Ψ - Φ) ↔ _
  rw [map_sub, choiLinear_apply, choiLinear_apply, sub_nonneg]

/-- A positive real rescaling preserves the support relation exactly. -/
theorem suppLE_smul_iff [Nontrivial B] (ρ σ : L B) {c : ℂ} (hc : c ≠ 0) :
    suppLE (c • ρ) (c • σ) ↔ suppLE ρ σ := by
  simp only [suppLE, LinearMap.ker_smul _ c hc]

/-- Scaling a vector scales its rank-one operator by the squared real scalar. -/
theorem outer_product_real_smul (v : A) (c : ℝ) :
    outer_product ((c : ℂ) • v) ((c : ℂ) • v) = ((c * c : ℝ) : ℂ) • outer_product v v := by
  ext x
  simp only [outer_product_eq_rankOne]
  change (inner ℂ ((c : ℂ) • v) x) • ((c : ℂ) • v) =
    ((c * c : ℝ) : ℂ) • ((inner ℂ v x) • v)
  rw [inner_smul_left, Complex.conj_ofReal, smul_smul, smul_smul, Complex.ofReal_mul]
  congr 1
  ring

variable [Nontrivial A] [Nontrivial B]

/-- Vectorization of the identity, before normalization. -/
noncomputable def choiVector (A : Type u) [Qudit A] : A ⊗[ℂ] A :=
  vec (stdOrthonormalBasis ℂ A).toBasis (LinearMap.id : L A)

theorem choiVector_ne_zero : choiVector A ≠ 0 := by
  intro h
  have he : (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis) (LinearMap.id : L A) = 0 := h
  have hid : (LinearMap.id : L A) = 0 :=
    (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis).injective (by simpa using he)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact ha (LinearMap.congr_fun hid a)

/-- A genuine normalized maximally-entangled input on the reference copy. -/
noncomputable def choiInput (A : Type u) [Qudit A] [Nontrivial A] : PureInput (A ⊗[ℂ] A) where
  vector := ((‖choiVector A‖⁻¹ : ℝ) : ℂ) • choiVector A
  norm_one := by
    simpa only [Complex.ofReal_inv] using
      (norm_smul_inv_norm (𝕜 := ℂ) (choiVector_ne_zero (A := A)))

/-- The density of the normalized Choi input. -/
theorem choiInput_density :
    (choiInput A).density.op =
      ((‖choiVector A‖⁻¹ * ‖choiVector A‖⁻¹ : ℝ) : ℂ) •
        outer_product (choiVector A) (choiVector A) :=
  outer_product_real_smul _ _

/-- Applying a channel to the normalized Choi input gives its normalized Choi operator. -/
theorem amplifiedOutput_choiInput (N : CPTP A B) :
    (amplifiedOutput N (choiInput A).density).op =
      ((‖choiVector A‖⁻¹ * ‖choiVector A‖⁻¹ : ℝ) : ℂ) •
        choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap := by
  change amplifyWithId N.toLinearMap _ = _
  rw [choiInput_density, map_smul]
  rfl

/-- The normalized input has exactly the support relation of the Choi pair. -/
theorem choiInput_support_iff (N M : CPTP A B) :
    suppLE (amplifiedOutput N (choiInput A).density).op
      (amplifiedOutput M (choiInput A).density).op ↔
    suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap) := by
  rw [amplifiedOutput_choiInput, amplifiedOutput_choiInput]
  exact suppLE_smul_iff _ _ (by
    exact_mod_cast mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr choiVector_ne_zero))
      (inv_ne_zero (norm_ne_zero_iff.mpr choiVector_ne_zero)))

/-- Choi support inclusion gives a finite, strictly positive CP domination constant. -/
theorem exists_cp_domination_of_choi_support (N M : CPTP A B)
    (hs : suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap)) :
    ∃ c : ℝ, 0 < c ∧ CPLe N.toLinearMap (c • M.toLinearMap) := by
  let b := (stdOrthonormalBasis ℂ A).toBasis
  have hN : 0 ≤ choi b N.toLinearMap := cp_to_choi b N.toLinearMap
    ⟨N.toCompletelyPositiveMap, rfl⟩
  have hM : 0 ≤ choi b M.toLinearMap := cp_to_choi b M.toLinearMap
    ⟨M.toCompletelyPositiveMap, rfl⟩
  obtain ⟨c, hc, hle⟩ := nonneg_le_smul_of_suppLE hN hM hs
  refine ⟨c, hc, (cpLe_iff_choi_le b _ _).mpr ?_⟩
  have hsmul : c • M.toLinearMap = (c : ℂ) • M.toLinearMap :=
    (IsScalarTower.algebraMap_smul ℂ c M.toLinearMap).symm
  rw [hsmul]
  change choi b N.toLinearMap ≤ choiLinear b ((c : ℂ) • M.toLinearMap)
  simpa only [map_smul, choiLinear_apply] using hle

/-- Every channel pair either has finite CP domination or an actual pure
stabilized input with support mismatch. This is an unconditional dichotomy. -/
theorem cp_domination_or_support_mismatch (N M : CPTP A B) :
    (∃ c : ℝ, 0 < c ∧ CPLe N.toLinearMap (c • M.toLinearMap)) ∨
      ∃ ψ : PureInput (A ⊗[ℂ] A),
        ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op := by
  classical
  by_cases hs : suppLE (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap)
      (choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap)
  · exact Or.inl (exists_cp_domination_of_choi_support N M hs)
  · exact Or.inr ⟨choiInput A, fun h => hs ((choiInput_support_iff N M).mp h)⟩

end QuantumChannelContinuity
