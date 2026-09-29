import QuantumChannelContinuity.TensorStates

/-! # Product inputs and superadditivity of concrete stabilized divergences -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {A B C D : Type u} [Qudit A] [Qudit B] [Qudit C] [Qudit D]

@[simp] theorem dilationRegroup_symm_tmul (a : A) (b : B) (c : C) (d : D) :
    (dilationRegroup (B := A) (E := B) (D := C) (F := D)).symm
      ((a ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] d)) =
      (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d) := by
  apply (dilationRegroup (B := A) (E := B) (D := C) (F := D)).injective
  simp

/-- Four operator tensor factors follow the same canonical regrouping as vectors. -/
theorem isoConj_regroup (X : L A) (Y : L B) (Z : L C) (W : L D) :
    isoConj dilationRegroup (TensorProduct.map (TensorProduct.map X Y) (TensorProduct.map Z W)) =
      TensorProduct.map (TensorProduct.map X Z) (TensorProduct.map Y W) := by
  ext a c b d
  simp [TensorProduct.map_tmul]

theorem outer_tensor (x x' : A) (y y' : B) :
    outer_product (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') =
      TensorProduct.map (outer_product x x') (outer_product y y') := by
  rw [← l_tensor_equiv_symm_outer_product, l_tensor_equiv_symm_tmul]

noncomputable def PureInput.tensor (ψ : PureInput A) (φ : PureInput B) : PureInput (A ⊗[ℂ] B) :=
  ⟨ψ.vector ⊗ₜ[ℂ] φ.vector, by rw [TensorProduct.norm_tmul, ψ.norm_one, φ.norm_one, mul_one]⟩

@[simp] theorem PureInput.density_tensor [Nontrivial A] [Nontrivial B]
    (ψ : PureInput A) (φ : PureInput B) :
    (ψ.tensor φ).density = ψ.density.tensor φ.density := by
  apply DensityState.ext
  exact outer_tensor _ _ _ _

/-- Product stabilized outputs, with the reference factors moved to the end. -/
theorem amplify_tensor_regroup (N : CPTP A B) (K : CPTP C D)
    (X : L (A ⊗[ℂ] A)) (Y : L (C ⊗[ℂ] C)) :
    amplifyWithId (tensorChannel N K).toLinearMap
        (isoConj dilationRegroup (TensorProduct.map X Y)) =
      isoConj dilationRegroup
        (TensorProduct.map (amplifyWithId N.toLinearMap X) (amplifyWithId K.toLinearMap Y)) := by
  obtain ⟨x, rfl⟩ := (l_tensor_equiv (ℋ₁ := A) (ℋ₂ := A)).symm.surjective X
  obtain ⟨y, rfl⟩ := (l_tensor_equiv (ℋ₁ := C) (ℋ₂ := C)).symm.surjective Y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul X₁ X₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul Y₁ Y₂ =>
      simp only [l_tensor_equiv_symm_tmul, isoConj_regroup, amplifyWithId_tensor]
      change TensorProduct.map (tensorSuperoperator N.toLinearMap K.toLinearMap
        (TensorProduct.map X₁ Y₁)) (TensorProduct.map X₂ Y₂) = _
      rw [tensorSuperoperator_apply]
      rfl
    | add y z hy hz => simp_all [TensorProduct.map_add_right]
  | add x z hx hz => simp_all [TensorProduct.map_add_left]

variable [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

/-- A product of independently optimized entangled inputs is an admissible
pure input for the tensor-product channel. -/
noncomputable def PureInput.stabilizedProduct (ψ : PureInput (A ⊗[ℂ] A))
    (φ : PureInput (C ⊗[ℂ] C)) : PureInput ((A ⊗[ℂ] C) ⊗[ℂ] (A ⊗[ℂ] C)) :=
  (ψ.tensor φ).mapIso dilationRegroup

theorem amplifiedOutput_product (N : CPTP A B) (K : CPTP C D)
    (ψ : PureInput (A ⊗[ℂ] A)) (φ : PureInput (C ⊗[ℂ] C)) :
    amplifiedOutput (tensorChannel N K) (ψ.stabilizedProduct φ).density =
      ((amplifiedOutput N ψ.density).tensor (amplifiedOutput K φ.density)).map
        (isometryChannel dilationRegroup) := by
  apply DensityState.ext
  rw [PureInput.stabilizedProduct, PureInput.density_mapIso, PureInput.density_tensor]
  exact amplify_tensor_regroup N K ψ.density.op φ.density.op

/-- Superadditivity under channel tensor products, in the actual stabilized
support-aware definitions and including infinite values. -/
theorem channelRenyi_tensor_superadditive {p : ℝ} (hp : 1 < p)
    (N M : CPTP A B) (K L : CPTP C D) :
    channelRenyi p N M + channelRenyi p K L ≤
      channelRenyi p (tensorChannel N K) (tensorChannel M L) := by
  apply ENNReal.iSup_add_iSup_le
  intro ψ φ
  have h := stateRenyi_le_channel (tensorChannel N K) (tensorChannel M L) p
    (ψ.stabilizedProduct φ)
  rw [amplifiedOutput_product N K, amplifiedOutput_product M L,
    stateRenyi_isometry (by linarith) hp.ne', stateRenyi_tensor hp,
    EReal.toENNReal_add (stateRenyi_nonneg (by linarith) hp.ne' _ _)
      (stateRenyi_nonneg (by linarith) hp.ne' _ _)] at h
  exact h

end QuantumChannelContinuity
