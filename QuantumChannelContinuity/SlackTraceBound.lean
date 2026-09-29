import QuantumChannelContinuity.SlackTester
import QuantumChannelContinuity.SDPPartialTrace

/-! # From a Choi marginal bound to the uniform pure-input trace bound -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B : Type u} [Qudit A] [Qudit B]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

theorem environment_gram (S : L A) :
    (LinearMap.adjoint (environmentMap (B := B) S)).comp (environmentMap (B := B) S) =
      environmentMap (B := B) ((LinearMap.adjoint S).comp S) := by
  simp [environmentMap,TensorProduct.adjoint_map,← TensorProduct.map_comp]

/-- The trace of a weighted Choi operator is the pairing with its reference marginal. -/
theorem trace_weighted_choi (X : L (B ⊗[ℂ] A)) (S : L A) :
    Tr (krausTerm (environmentMap (B := B) S) X) =
      Tr (((LinearMap.adjoint S).comp S) * leftPartialTrace X) := by
  let U := environmentMap (B := B) S
  have hcycle : Tr (krausTerm U X) = Tr (((LinearMap.adjoint U).comp U).comp X) := by
    have h := LinearMap.trace_comp_comm' (U.comp X) (LinearMap.adjoint U)
    simpa only [krausTerm,LinearMap.comp_assoc] using h.symm
  rw [hcycle]
  change Tr (((LinearMap.adjoint (environmentMap (B := B) S)).comp
    (environmentMap (B := B) S)).comp X) = _
  rw [environment_gram]
  exact (leftPartialTrace_pair X ((LinearMap.adjoint S).comp S)).symm

variable [Nontrivial A]

/-- A Choi marginal bound controls the trace for every entangled pure input. -/
theorem amplified_trace_le_of_choi_marginal (Φ : T A B) (ε : ℝ)
    (hbound : leftPartialTrace (choi (stdOrthonormalBasis ℂ A).toBasis Φ) ≤
      (ε : ℂ) • (1 : L A)) (ψ : A ⊗[ℂ] A) :
    (Tr (amplifyWithId Φ (outer_product ψ ψ))).re ≤ ε * ‖ψ‖ ^ 2 := by
  obtain ⟨S,rfl⟩ := reference_choiVector_surjective (A := A) ψ
  rw [amplify_weighted_choi,trace_weighted_choi,norm_reference_choiVector_sq]
  let G : L A := (LinearMap.adjoint S).comp S
  have hG : 0 ≤ G := by change 0 ≤ star S * S; exact star_mul_self_nonneg S
  have hp := trace_product_nonneg hG (sub_nonneg.mpr hbound)
  simp only [mul_sub,mul_smul_comm,mul_one,map_sub,map_smul,Complex.sub_re,
    smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hp
  exact sub_nonneg.mp hp

/-- In particular, the Choi marginal bound gives the exact vector trace
inequality used by `HockeySlackAttainment`, without a dimension factor. -/
theorem trace_le_of_choi_marginal (Φ : T A B) (ε : ℝ)
    (hbound : leftPartialTrace (choi (stdOrthonormalBasis ℂ A).toBasis Φ) ≤
      (ε : ℂ) • (1 : L A)) (a : A) :
    (Tr (Φ (outer_product a a))).re ≤ ε * ‖a‖ ^ 2 := by
  let r : PureInput A := Classical.choice inferInstance
  have h := amplified_trace_le_of_choi_marginal Φ ε hbound (a ⊗ₜ[ℂ] r.vector)
  have htrace : Tr (amplifyWithId Φ (outer_product (a ⊗ₜ[ℂ] r.vector) (a ⊗ₜ[ℂ] r.vector))) =
      Tr (Φ (outer_product a a)) := by
    rw [← l_tensor_equiv_symm_outer_product,l_tensor_equiv_symm_tmul]
    change Tr (tensorSuperoperator Φ (LinearMap.id : T A A)
      (TensorProduct.map (outer_product a a) (outer_product r.vector r.vector))) = _
    rw [tensorSuperoperator_apply,LinearMap.trace_tensorProduct']
    change Tr (Φ (outer_product a a)) * Tr r.density.op = _
    rw [r.density.trace_one,mul_one]
  rw [htrace,TensorProduct.norm_tmul,r.norm_one,mul_one] at h
  exact h

end QuantumChannelContinuity
