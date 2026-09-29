import QuantumChannelContinuity.TensorChannels
import QuantumChannelContinuity.FilterTensor

/-!
# Tensor products of prescribed Stinespring dilations

The output and environment factors are regrouped by a Hilbert-space isometry.
The resulting channel is exactly the tensor product, and its operator norm is
bounded by the product of the original dilation norms.
-/

open QuantumState QuantumChannel
open scoped TensorProduct ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {A B C D E F : Type u}
  [Qudit A] [Qudit B] [Qudit C] [Qudit D] [Qudit E] [Qudit F]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- Regroup the two output factors and the two environment factors. -/
noncomputable def dilationRegroup :
    (B ⊗[ℂ] E) ⊗[ℂ] (D ⊗[ℂ] F) ≃ₗᵢ[ℂ] (B ⊗[ℂ] D) ⊗[ℂ] (E ⊗[ℂ] F) :=
  (TensorProduct.assocIsometry ℂ B E (D ⊗[ℂ] F)).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.assocIsometry ℂ E D F).symm).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E D)
        (LinearIsometryEquiv.refl ℂ F))).trans
    ((TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ B)
      (TensorProduct.assocIsometry ℂ D E F)).trans
      (TensorProduct.assocIsometry ℂ B D (E ⊗[ℂ] F)).symm)))

@[simp] theorem dilationRegroup_tmul (b : B) (e : E) (d : D) (f : F) :
    dilationRegroup ((b ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] (d ⊗ₜ[ℂ] f)) =
      (b ⊗ₜ[ℂ] d) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] f) := by
  simp [dilationRegroup]

/-- Tensor two dilations while retaining all environment degrees of freedom. -/
noncomputable def tensorDilation (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    A ⊗[ℂ] C →ₗ[ℂ] (B ⊗[ℂ] D) ⊗[ℂ] (E ⊗[ℂ] F) :=
  dilationRegroup.toLinearMap.comp (TensorProduct.map U W)

@[simp] theorem tensorDilation_tmul (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) (a : A) (c : C) :
    tensorDilation U W (a ⊗ₜ[ℂ] c) = dilationRegroup (U a ⊗ₜ[ℂ] W c) := by
  simp [tensorDilation]

/-- Exact Kraus expansion using any chosen environment orthonormal basis. -/
theorem dilationChannel_kraus_basis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (U : A →ₗ[ℂ] B ⊗[ℂ] E) (X : L A) :
    dilationChannel U X = ∑ i, krausTerm (tensorRightSlice b i ∘ₗ U) X := by
  classical
  unfold dilationChannel
  rw [LinearMap.comp_apply, TrRight_eq_kraus_sum b]
  apply Finset.sum_congr rfl
  intro i _
  simp [krausTerm, LinearMap.adjoint_comp, LinearMap.comp_assoc]

theorem slice_dilationRegroup {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    (i : ι) (j : κ) (x : B ⊗[ℂ] E) (y : D ⊗[ℂ] F) :
    tensorRightSlice (b.tensorProduct c) (i,j) (dilationRegroup (x ⊗ₜ[ℂ] y)) =
      tensorRightSlice b i x ⊗ₜ[ℂ] tensorRightSlice c j y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul w f =>
      simp [tensorRightSlice_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        smul_smul, mul_comm]
    | add y z hy hz => simp_all [TensorProduct.tmul_add]
  | add x y hx hy => simp_all [TensorProduct.add_tmul]

theorem tensorDilation_slice {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ F)
    (U : A →ₗ[ℂ] B ⊗[ℂ] E) (W : C →ₗ[ℂ] D ⊗[ℂ] F) (i : ι) (j : κ) :
    tensorRightSlice (b.tensorProduct c) (i,j) ∘ₗ tensorDilation U W =
      TensorProduct.map (tensorRightSlice b i ∘ₗ U) (tensorRightSlice c j ∘ₗ W) := by
  ext a c'
  simp [slice_dilationRegroup]

/-- The tensor of supplied dilations realizes the tensor of their channels. -/
theorem dilationChannel_tensorDilation (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    dilationChannel (tensorDilation U W) =
      tensorSuperoperator (dilationChannel U) (dilationChannel W) := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let c := stdOrthonormalBasis ℂ F
  apply LinearMap.ext
  intro Z
  obtain ⟨z, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := C)).symm.surjective Z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul X Y =>
    rw [l_tensor_equiv_symm_tmul, tensorSuperoperator_apply,
      dilationChannel_kraus_basis (b.tensorProduct c), dilationChannel_kraus_basis b,
      dilationChannel_kraus_basis c, Fintype.sum_prod_type]
    simp_rw [tensorDilation_slice, tensor_kraus_apply]
    ext a c'
    simp [TensorProduct.sum_tmul, TensorProduct.tmul_sum, krausTerm]
    exact Finset.sum_comm
  | add x y hx hy => simp_all

/-- Hilbert-space operator-norm submultiplicativity for the tensor dilation. -/
theorem tensorDilation_norm_le (U : A →ₗ[ℂ] B ⊗[ℂ] E)
    (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    ‖(tensorDilation U W).toContinuousLinearMap‖ ≤
      ‖U.toContinuousLinearMap‖ * ‖W.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg U.toContinuousLinearMap) (norm_nonneg W.toContinuousLinearMap))
  intro ψ
  change ‖dilationRegroup (TensorProduct.map U W ψ)‖ ≤ _
  rw [dilationRegroup.norm_map]
  exact ((TensorProduct.map U W).toContinuousLinearMap.le_opNorm ψ).trans
    (mul_le_mul_of_nonneg_right (tensorMap_norm_le U W) (norm_nonneg ψ))

/-- Tensor dilation is linear in the left family of summands. -/
theorem tensorDilation_sum_left {ι : Type*} [Fintype ι]
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (W : C →ₗ[ℂ] D ⊗[ℂ] F) :
    tensorDilation (∑ i, U i) W = ∑ i, tensorDilation (U i) W := by
  ext a c
  simp [TensorProduct.sum_tmul]

/-- Tensor dilation is linear in the right family of summands. -/
theorem tensorDilation_sum_right {ι : Type*} [Fintype ι]
    (U : A →ₗ[ℂ] B ⊗[ℂ] E) (W : ι → C →ₗ[ℂ] D ⊗[ℂ] F) :
    tensorDilation U (∑ i, W i) = ∑ i, tensorDilation U (W i) := by
  ext a c
  simp [TensorProduct.tmul_sum]

end QuantumChannelContinuity
