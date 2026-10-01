/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.SDPTrace
import QuantumChannelContinuity.ChoiSupport
import QuantumChannelContinuity.TensorChannels

/-! # Choi dual effects as physical channel tests -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B R : Type u} [Qudit A] [Qudit B] [Qudit R]
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- A reference operation commutes exactly with channel amplification. -/
theorem tensorSuperoperator_reference_kraus (Φ : T A B) (S : L R)
    (X : L (A ⊗[ℂ] R)) :
    tensorSuperoperator Φ (LinearMap.id : T R R)
        (krausTerm (environmentMap (B := A) S) X) =
      krausTerm (environmentMap (B := B) S)
        (tensorSuperoperator Φ (LinearMap.id : T R R) X) := by
  obtain ⟨x,rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := R)).symm.surjective X
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul U V =>
    rw [l_tensor_equiv_symm_tmul]
    simp only [environmentMap]
    rw [tensor_kraus_apply,tensorSuperoperator_apply,tensorSuperoperator_apply,tensor_kraus_apply]
    simp [krausTerm]
  | add x y hx hy => simp_all

/-- Applying the reference map to the Choi vector gives a purification whose
squared norm is exactly the Gram trace of the reference map. -/
theorem norm_reference_choiVector_sq (S : L A) :
    ‖environmentMap (B := A) S (choiVector A)‖ ^ 2 =
      (Tr ((LinearMap.adjoint S).comp S)).re := by
  have hv : environmentMap (B := A) S (choiVector A) =
      TensorProduct.comm ℂ A A (vec (stdOrthonormalBasis ℂ A).toBasis S) := by
    simp [choiVector,vec_apply,environmentMap]
  rw [hv,TensorProduct.norm_comm]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ),inner_vec_eq_trace]
  rfl

/-- An actual pure-input output is a weighted Choi operator. -/
theorem amplify_weighted_choi (Φ : T A B) (S : L A) :
    amplifyWithId Φ
      (outer_product (environmentMap (B := A) S (choiVector A))
        (environmentMap (B := A) S (choiVector A))) =
      krausTerm (environmentMap (B := B) S) (choi (stdOrthonormalBasis ℂ A).toBasis Φ) := by
  rw [← comp_outer_product_adjoint]
  change tensorSuperoperator Φ (LinearMap.id : T A A)
      (krausTerm (environmentMap (B := A) S) (outer_product (choiVector A) (choiVector A))) = _
  rw [tensorSuperoperator_reference_kraus]
  rfl

/-- The reference square-root map has exactly the prescribed Gram operator. -/
theorem environment_sqrt_gram (Y : L A) (hY : 0 ≤ Y) :
    (LinearMap.adjoint (environmentMap (B := B) (CFC.sqrt Y))).comp
        (environmentMap (B := B) (CFC.sqrt Y)) = environmentMap (B := B) Y := by
  simp only [environmentMap,TensorProduct.adjoint_map,← TensorProduct.map_comp,
    LinearMap.adjoint_id,LinearMap.id_comp]
  congr 1
  change star (CFC.sqrt Y) * CFC.sqrt Y = Y
  rw [(CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq]
  exact CFC.sqrt_mul_sqrt_self Y hY

/-- Every operator below an identity-tensored positive operator is a physical
effect in the corresponding purification, even if the reference is singular. -/
theorem exists_choi_effect (W : L (B ⊗[ℂ] A)) (Y : L A)
    (hW : 0 ≤ W) (hY : 0 ≤ Y) (hle : W ≤ environmentMap (B := B) Y) :
    ∃ T : Effect (B ⊗[ℂ] A), W =
      (LinearMap.adjoint (environmentMap (B := B) (CFC.sqrt Y))).comp
        (T.op.comp (environmentMap (B := B) (CFC.sqrt Y))) := by
  let S := environmentMap (B := B) (CFC.sqrt Y)
  have hWgram : (LinearMap.adjoint (CFC.sqrt W)).comp (CFC.sqrt W) = W := by
    change star (CFC.sqrt W) * CFC.sqrt W = W
    rw [(CFC.sqrt_nonneg W).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self W hW
  obtain ⟨U,hU,hUS⟩ := exists_contraction_factor_of_gram_le (CFC.sqrt W) S (by
    rw [hWgram,environment_sqrt_gram Y hY]
    exact hle)
  let T : Effect (B ⊗[ℂ] A) := ⟨(LinearMap.adjoint U).comp U,
    by change 0 ≤ star U * U; exact star_mul_self_nonneg U,hU⟩
  refine ⟨T,?_⟩
  rw [← hWgram,hUS,LinearMap.adjoint_comp]
  simp only [T,LinearMap.comp_assoc]
  rfl

/-- The dual Choi objective is the acceptance difference of the resulting test. -/
theorem trace_choi_effect (W : L (B ⊗[ℂ] A)) (S : L (B ⊗[ℂ] A))
    (T : Effect (B ⊗[ℂ] A)) (hW : W = (LinearMap.adjoint S).comp (T.op.comp S))
    (X : L (B ⊗[ℂ] A)) : Tr (W * X) = Tr (T.op * krausTerm S X) := by
  rw [hW]
  change Tr ((LinearMap.adjoint S).comp ((T.op.comp S).comp X)) =
    Tr (T.op.comp (S.comp (X.comp (LinearMap.adjoint S))))
  rw [LinearMap.trace_comp_comm']
  simp only [LinearMap.comp_assoc]

variable [Nontrivial A] [Nontrivial B]

/-- A normalized feasible Choi dual pair is a genuine pure-input channel test. -/
theorem normalized_choi_test_le_hockey (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ)
    (W : L (B ⊗[ℂ] A)) (Y : L A) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hle : W ≤ environmentMap (B := B) Y) (htr : (Tr Y).re = 1) :
    (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
      (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re ≤
      channelHockey γ N M := by
  have hgram : (LinearMap.adjoint (CFC.sqrt Y)).comp (CFC.sqrt Y) = Y := by
    change star (CFC.sqrt Y) * CFC.sqrt Y = Y
    rw [(CFC.sqrt_nonneg Y).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self Y hY
  have hnorm : ‖environmentMap (B := A) (CFC.sqrt Y) (choiVector A)‖ = 1 := by
    have h := norm_reference_choiVector_sq (CFC.sqrt Y)
    rw [hgram,htr] at h
    nlinarith [norm_nonneg (environmentMap (B := A) (CFC.sqrt Y) (choiVector A))]
  let ψ : PureInput (A ⊗[ℂ] A) := ⟨environmentMap (B := A) (CFC.sqrt Y) (choiVector A),hnorm⟩
  obtain ⟨T,hT⟩ := exists_choi_effect W Y hW hY hle
  have hprob (Φ : CPTP A B) :
      (Tr (W * choi (stdOrthonormalBasis ℂ A).toBasis Φ.toLinearMap)).re =
        T.probability (amplifiedOutput Φ ψ.density) := by
    rw [trace_choi_effect W (environmentMap (B := B) (CFC.sqrt Y)) T hT]
    rw [← amplify_weighted_choi]
    rfl
  have hobj :
      (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
        (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re =
      T.probability (amplifiedOutput N ψ.density) - γ *
        T.probability (amplifiedOutput M ψ.density) := by
    simp only [mul_sub,map_sub,Complex.sub_re,mul_smul_comm,map_smul,smul_eq_mul,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hprob]
  rw [hobj]
  apply le_trans (le_csSup (s := Set.range (fun T : Effect (B ⊗[ℂ] A) =>
    T.probability (amplifiedOutput N ψ.density) - γ * T.probability (amplifiedOutput M ψ.density)))
    ⟨1, by rintro _ ⟨T,rfl⟩; exact hockey_objective_le_one hγ _ _ T⟩ (Set.mem_range_self T))
  apply le_csSup (s := Set.range (fun φ : PureInput (A ⊗[ℂ] A) =>
    stateHockey γ (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)))
    ⟨1, by rintro _ ⟨φ,rfl⟩; exact stateHockey_le_one hγ _ _⟩ (Set.mem_range_self ψ)

/-- Every bipartite vector arises by applying a reference operator to the Choi vector. -/
theorem reference_choiVector_surjective :
    Function.Surjective (fun S : L A => environmentMap (B := A) S (choiVector A)) := by
  intro ψ
  obtain ⟨S,hS⟩ := (vecLinearEquiv (stdOrthonormalBasis ℂ A).toBasis).surjective
    (TensorProduct.comm ℂ A A ψ)
  refine ⟨S,?_⟩
  have hv : environmentMap (B := A) S (choiVector A) =
      TensorProduct.comm ℂ A A (vec (stdOrthonormalBasis ℂ A).toBasis S) := by
    simp [choiVector,vec_apply,environmentMap]
  change environmentMap (B := A) S (choiVector A) = ψ
  rw [hv,show vec (stdOrthonormalBasis ℂ A).toBasis S = TensorProduct.comm ℂ A A ψ from hS]
  simp

/-- Every feasible, possibly unnormalized Choi dual pair is bounded by the
actual stabilized channel hockey-stick divergence times its normalization. -/
theorem choi_test_le_hockey (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ)
    (W : L (B ⊗[ℂ] A)) (Y : L A) (hW : 0 ≤ W) (hY : 0 ≤ Y)
    (hle : W ≤ environmentMap (B := B) Y) :
    (Tr (W * (choi (stdOrthonormalBasis ℂ A).toBasis N.toLinearMap -
      (γ : ℂ) • choi (stdOrthonormalBasis ℂ A).toBasis M.toLinearMap))).re ≤
      channelHockey γ N M * (Tr Y).re := by
  by_cases hY0 : Y = 0
  · have hW0 : W = 0 := le_antisymm (by simpa [hY0,environmentMap] using hle) hW
    simp [hY0,hW0]
  have hc : 0 < (Tr Y).re := trace_re_pos_of_ne_zero hY hY0
  let c := (Tr Y).re
  have hcn : (0 : ℂ) ≤ (c⁻¹ : ℝ) := by exact_mod_cast (inv_nonneg.mpr hc.le)
  let W' := ((c⁻¹ : ℝ) : ℂ) • W
  let Y' := ((c⁻¹ : ℝ) : ℂ) • Y
  have hle' : W' ≤ environmentMap (B := B) Y' := by
    have heq : environmentMap (B := B) Y' = ((c⁻¹ : ℝ) : ℂ) • environmentMap (B := B) Y := by
      exact TensorProduct.map_smul_right _ _ _
    rw [heq]
    exact smul_le_smul_of_nonneg_left hle hcn
  have htr : (Tr Y').re = 1 := by
    simp [Y',c,Complex.mul_re,hc.ne']
  have h := normalized_choi_test_le_hockey N M hγ W' Y'
    (smul_nonneg hcn hW) (smul_nonneg hcn hY) hle' htr
  have heq (X : L (B ⊗[ℂ] A)) :
      (Tr (W' * X)).re = c⁻¹ * (Tr (W * X)).re := by
    simp [W',Complex.mul_re]
  rw [heq] at h
  simpa only [mul_comm] using (inv_mul_le_iff₀ hc).mp h

end QuantumChannelContinuity
