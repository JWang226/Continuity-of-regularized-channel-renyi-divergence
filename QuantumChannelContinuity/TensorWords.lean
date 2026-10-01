/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorDilation
import QuantumChannelContinuity.TensorOrder
import QuantumChannelContinuity.Regularization
import QuantumChannelContinuity.DivergenceSchatten

/-!
# Actual tensor-word dilations

Words are tensor products of supplied dilation pieces.  Their sum realizes the
actual channel power used in `Regularization`; the domination and norm constants
are the products of the one-block constants.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

def DilationUnit := EuclideanSpace ℂ (Fin 1)
noncomputable instance : Qudit DilationUnit := inferInstanceAs (Qudit (EuclideanSpace ℂ (Fin 1)))

/-- The zero-copy dilation, in exactly the unit spaces used by `TensorPower`. -/
noncomputable def unitDilation : DilationUnit →ₗ[ℂ] DilationUnit ⊗[ℂ] DilationUnit :=
  (TensorProduct.mk ℂ DilationUnit DilationUnit).flip (EuclideanSpace.single 0 1)

@[simp] theorem unitDilation_apply (x : DilationUnit) :
    unitDilation x = x ⊗ₜ[ℂ] EuclideanSpace.single 0 1 := rfl

/-- The zero-copy dilation realizes the identity unit channel. -/
theorem dilationChannel_unitDilation : dilationChannel unitDilation = LinearMap.id := by
  have hslice : tensorRightSlice (EuclideanSpace.basisFun (Fin 1) ℂ) 0 ∘ₗ unitDilation =
      LinearMap.id := by
    ext x
    change tensorRightSlice (EuclideanSpace.basisFun (Fin 1) ℂ) 0
      (x ⊗ₜ[ℂ] EuclideanSpace.single 0 1) = x
    rw [tensorRightSlice_tmul]
    simp [EuclideanSpace.basisFun_toBasis]
  ext1 X
  rw [dilationChannel_kraus_basis (EuclideanSpace.basisFun (Fin 1) ℂ)]
  simp only [Fin.sum_univ_one, hslice]
  simp [krausTerm]

set_option backward.isDefEq.respectTransparency true in
theorem unitDilation_norm_le_one : ‖unitDilation.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖x ⊗ₜ[ℂ] EuclideanSpace.single (0 : Fin 1) (1 : ℂ)‖ ≤ _
  simp [TensorProduct.norm_tmul, EuclideanSpace.norm_single]

variable {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B] [Nontrivial E]

/-- The supplied dilation tensored `n` times in the canonical power spaces. -/
noncomputable def dilationPower (V : A →ₗ[ℂ] B ⊗[ℂ] E) :
    (n : ℕ) → TensorPower A n →ₗ[ℂ] TensorPower B n ⊗[ℂ] TensorPower E n
  | 0 => unitDilation
  | n + 1 => tensorDilation V (dilationPower V n)

/-- Exact identification with the concrete channel tensor powers. -/
theorem dilationChannel_dilationPower (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap) (n : ℕ) :
    dilationChannel (dilationPower V n) = (channelPower N n).toLinearMap := by
  induction n with
  | zero => exact dilationChannel_unitDilation
  | succ n ih =>
    change dilationChannel (tensorDilation V (dilationPower V n)) =
      tensorSuperoperator N.toLinearMap (channelPower N n).toLinearMap
    rw [dilationChannel_tensorDilation, hV, ih]

/-- Tensor-word dilation, retaining its concrete shared environment. -/
noncomputable def wordDilation {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) :
    (n : ℕ) → (Fin n → ι) →
      TensorPower A n →ₗ[ℂ] TensorPower B n ⊗[ℂ] TensorPower E n
  | 0, _ => unitDilation
  | n + 1, word => tensorDilation (U (word 0)) (wordDilation U n (fun j => word j.succ))

/-- Summing all tensor words reconstructs the full tensor-power dilation. -/
theorem wordDilation_sum {ι : Type*} [Fintype ι]
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (n : ℕ) :
    (∑ word : Fin n → ι, wordDilation U n word) = dilationPower (∑ i, U i) n := by
  classical
  induction n with
  | zero => simp [wordDilation, dilationPower]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp (wordDilation U (n+1)),
      Fintype.sum_prod_type]
    change (∑ i, ∑ word : Fin n → ι, tensorDilation (U i) (wordDilation U n word)) =
      tensorDilation (∑ i, U i) (dilationPower (∑ i, U i) n)
    calc
      _ = ∑ i, tensorDilation (U i) (∑ word : Fin n → ι, wordDilation U n word) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (tensorDilation_sum_right (U i) (wordDilation U n)).symm
      _ = _ := by rw [ih, ← tensorDilation_sum_left]

/-- The sum of words realizes the actual tensor-power channel on every input. -/
theorem dilationChannel_wordDilation_sum {ι : Type*} [Fintype ι]
    (N : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i) (n : ℕ) :
    dilationChannel (∑ word : Fin n → ι, wordDilation U n word) =
      (channelPower N n).toLinearMap := by
  rw [wordDilation_sum, ← hVU]
  exact dilationChannel_dilationPower N V hV n

/-- Product operator-norm bound, including the empty word. -/
theorem wordDilation_norm_le {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E)
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hU : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) (n : ℕ) (word : Fin n → ι) :
    ‖(wordDilation U n word).toContinuousLinearMap‖ ≤ ∏ j, b (word j) := by
  induction n with
  | zero => simpa [wordDilation] using unitDilation_norm_le_one
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (tensorDilation_norm_le _ _).trans
      (mul_le_mul (hU _) (ih _) (norm_nonneg (wordDilation U n (fun j => word j.succ)).toContinuousLinearMap) (hb _))

/-- Product CP-order bound against the actual channel power. -/
theorem wordDilation_cp_le {ι : Type*} (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E)
    (M : CPTP A B) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hU : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (n : ℕ) (word : Fin n → ι) :
    CPLe (dilationChannel (wordDilation U n word))
      ((∏ j, lam (word j)) • (channelPower M n).toLinearMap) := by
  induction n with
  | zero =>
    simp only [wordDilation, Fin.prod_univ_zero, one_smul]
    change CPLe (dilationChannel unitDilation) (LinearMap.id : T DilationUnit DilationUnit)
    rw [dilationChannel_unitDilation]
    change IsCompletelyPositive ((LinearMap.id : T DilationUnit DilationUnit) - LinearMap.id)
    rw [sub_self]
    simpa using cp_smul (cp_identity (C := DilationUnit)) (c := 0) le_rfl
  | succ n ih =>
    change CPLe (dilationChannel (tensorDilation (U (word 0))
      (wordDilation U n (fun j => word j.succ)))) _
    rw [dilationChannel_tensorDilation, Fin.prod_univ_succ]
    exact (hU _).tensor_scaled (ih _) (dilationChannel_cp _)
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩
      (Finset.prod_nonneg fun j _ => hlam _)

/-- The sum over tensor-word weights factors as the power of the one-block sum. -/
theorem word_weight_sum {ι : Type*} [Fintype ι] (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i) (p : ℝ) (m : ℕ) :
    (∑ word : Fin m → ι, (∏ j, b (word j)) ^ (1 / p) *
      (∏ j, lam (word j)) ^ ((p - 1) / (2 * p))) =
      (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))) ^ m := by
  classical
  have heq (word : Fin m → ι) :
      (∏ j, b (word j)) ^ (1 / p) * (∏ j, lam (word j)) ^ ((p - 1) / (2 * p)) =
      ∏ j, (b (word j) ^ (1 / p) * lam (word j) ^ ((p - 1) / (2 * p))) := by
    rw [← Real.finset_prod_rpow _ _ (fun j _ => hb (word j)),
      ← Real.finset_prod_rpow _ _ (fun j _ => hlam (word j)), Finset.prod_mul_distrib]
  simp_rw [heq]
  exact (Fintype.sum_pow (fun i => b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))) m).symm

/-- The full tensor-word Schatten estimate for actual channel powers.  There
are no word-level operator, CP-order, support, or input-reference hypotheses. -/
theorem blockRenyi_dilation_exponential_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) (m : ℕ) :
    blockRenyi p N M m ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (blockRenyi p N M m).toReal) ≤
      (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))) ^ m := by
  have h := channelRenyi_dilation_exponential_bound hp hp2 (channelPower N m) (channelPower M m)
    (dilationPower V m) (dilationChannel_dilationPower N V hV m)
    (wordDilation U m) (by rw [wordDilation_sum, ← hVU])
    (fun word => ∏ j, b (word j)) (fun word => ∏ j, lam (word j))
    (fun word => Finset.prod_nonneg fun j _ => hb (word j))
    (fun word => Finset.prod_nonneg fun j _ => hlam (word j))
    (wordDilation_cp_le U M lam hlam hdom m) (wordDilation_norm_le U b hb hnorm m)
  rwa [word_weight_sum b lam hb hlam p m] at h

/-- Uniform linear bound in block length, proved using the actual tensor
powers and the concrete tensor-word construction. -/
theorem blockRenyi_dilation_rate_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) (m : ℕ) :
    blockRenyi p N M m ≤ ENNReal.ofReal ((m : ℝ) * ((2 * p / (p - 1)) *
      Real.logb 2 (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))))) := by
  have h := channelRenyi_dilation_bound hp hp2 (channelPower N m) (channelPower M m)
    (dilationPower V m) (dilationChannel_dilationPower N V hV m)
    (wordDilation U m) (by rw [wordDilation_sum, ← hVU])
    (fun word => ∏ j, b (word j)) (fun word => ∏ j, lam (word j))
    (fun word => Finset.prod_nonneg fun j _ => hb (word j))
    (fun word => Finset.prod_nonneg fun j _ => hlam (word j))
    (wordDilation_cp_le U M lam hlam hdom m) (wordDilation_norm_le U b hb hnorm m)
  rw [word_weight_sum b lam hb hlam p m, Real.logb_pow] at h
  convert h using 1
  congr 1
  ring

/-- The complete finite-block filter/Schatten-to-regularization bridge. The
regularized quantity is the explicit block supremum from `Regularization`. -/
theorem regularizedRenyi_dilation_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    regularizedRenyi p N M ≤ ENNReal.ofReal ((2 * p / (p - 1)) *
      Real.logb 2 (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)))) := by
  apply iSup_le
  intro m
  apply iSup_le
  intro hm
  apply ENNReal.div_le_of_le_mul
  have h := blockRenyi_dilation_rate_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm m
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg m)] at h
  simpa only [ENNReal.ofReal_natCast, mul_comm] using h

end QuantumChannelContinuity
