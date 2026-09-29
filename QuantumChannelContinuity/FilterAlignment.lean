import QuantumChannelContinuity.Filter

/-!
# Alignment of supplied dilations

The environmental coefficient Gram matrix is recovered from the channel on
rank-one input operators.  Douglas factorization then aligns two supplied
dilations by a contraction, including nonminimal and singular dilations.
-/

open QuantumState QuantumChannel TensorProduct
open scoped ComplexOrder BigOperators

namespace QuantumChannelContinuity

universe u
variable {A B E F : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit F]

set_option maxHeartbeats 800000

/-- Extract an environmental coefficient against an output vector. -/
noncomputable def outputSlice (b : B) : B ⊗[ℂ] E →ₗ[ℂ] E :=
  (TensorProduct.lid ℂ E).toLinearMap.comp
    (TensorProduct.map (InnerProductSpace.toDualMap ℂ B b) LinearMap.id)

@[simp] theorem outputSlice_tmul (b x : B) (y : E) :
    outputSlice b (x ⊗ₜ[ℂ] y) = inner ℂ b x • y := by
  simp [outputSlice]

theorem trRight_outer_product_tmul (b c : B) (e f : E) :
    TrRight (outer_product (b ⊗ₜ[ℂ] e) (c ⊗ₜ[ℂ] f)) =
      inner ℂ e f • outer_product b c := by
  rw [← l_tensor_equiv_symm_outer_product, l_tensor_equiv_symm_tmul,
    trRight_map, trace_outer_product]

private theorem outer_product_add_left' (u v w : B ⊗[ℂ] E) :
    outer_product (u + v) w = outer_product u w + outer_product v w := by
  ext x
  simp [outer_product_eq_rankOne]

private theorem outer_product_add_right' (u v w : B ⊗[ℂ] E) :
    outer_product u (v + w) = outer_product u v + outer_product u w := by
  ext x
  simp [outer_product_eq_rankOne]

/-- Partial trace recovers the Gram products of environmental coefficients. -/
theorem inner_outputSlice (b c : B) (x y : B ⊗[ℂ] E) :
    inner ℂ (outputSlice b x) (outputSlice c y) =
      inner ℂ c ((TrRight (outer_product x y)) b) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [outer_product_eq_rankOne]
  | tmul d e =>
    induction y using TensorProduct.induction_on with
    | zero => simp [outer_product_eq_rankOne]
    | tmul f g =>
      rw [trRight_outer_product_tmul]
      simp only [outputSlice_tmul, inner_smul_left, inner_smul_right,
        LinearMap.smul_apply, outer_product_eq_rankOne,
        ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]
      simp only [inner_conj_symm]
      ring
    | add y z hy hz =>
      simp only [map_add, inner_add_right, outer_product_add_right',
        LinearMap.add_apply, hy, hz]
  | add x z hx hz =>
    simp only [map_add, inner_add_left, outer_product_add_left',
      LinearMap.add_apply, inner_add_right, hx, hz]

theorem outputSlice_environmentMap (U : E →ₗ[ℂ] F) (b : B) (x : B ⊗[ℂ] E) :
    outputSlice b (environmentMap U x) = U (outputSlice b x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d e => simp [environmentMap]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem outputSlice_expand {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ B) (x : B ⊗[ℂ] E) :
    x = ∑ i, b i ⊗ₜ[ℂ] outputSlice (b i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d e =>
    calc
      d ⊗ₜ[ℂ] e = (∑ i, b.repr d i • b i) ⊗ₜ[ℂ] e := by rw [b.sum_repr]
      _ = _ := by
        simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul', outputSlice_tmul,
          TensorProduct.tmul_smul, b.repr_apply_apply]
  | add x y hx hy =>
    simpa only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib] using
      congrArg₂ (· + ·) hx hy

theorem outputSlice_ext {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ B) {x y : B ⊗[ℂ] E}
    (h : ∀ i, outputSlice (b i) x = outputSlice (b i) y) : x = y := by
  rw [outputSlice_expand b x, outputSlice_expand b y]
  simp only [h]

theorem dilationChannel_outer_product (V : A →ₗ[ℂ] B ⊗[ℂ] E) (a c : A) :
    dilationChannel V (outer_product a c) = TrRight (outer_product (V a) (V c)) := by
  simp only [dilationChannel, LinearMap.comp_apply, krausTerm,
    LinearMap.coe_mk, AddHom.coe_mk, comp_outer_product_adjoint]

/-- Equal channels give the same environmental coefficient Gram products. -/
theorem dilation_coefficient_gram
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (hVW : dilationChannel V = dilationChannel W) (a c : A) (b d : B) :
    inner ℂ (outputSlice b (V a)) (outputSlice d (V c)) =
      inner ℂ (outputSlice b (W a)) (outputSlice d (W c)) := by
  rw [inner_outputSlice, inner_outputSlice]
  have h := congrArg (fun Φ : QuantumChannel.T A B => Φ (outer_product a c)) hVW
  dsimp only at h
  rw [dilationChannel_outer_product, dilationChannel_outer_product] at h
  rw [h]

/-- Reshuffle a supplied dilation into its environmental coefficient map. -/
noncomputable def dilationCoefficients {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) : A ⊗[ℂ] B →ₗ[ℂ] E :=
  (a.tensorProduct b).toBasis.constr ℂ (fun p => outputSlice (b p.2) (V (a p.1)))

@[simp] theorem dilationCoefficients_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (i : ι) (j : κ) :
    dilationCoefficients a b V (a i ⊗ₜ[ℂ] b j) = outputSlice (b j) (V (a i)) := by
  simpa only [dilationCoefficients, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.tensorProduct_apply] using
    (a.tensorProduct b).toBasis.constr_basis ℂ
      (fun p => outputSlice (b p.2) (V (a p.1))) (i, j)

theorem dilationCoefficients_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (hVW : dilationChannel V = dilationChannel W) (x y : A ⊗[ℂ] B) :
    inner ℂ (dilationCoefficients a b V x) (dilationCoefficients a b V y) =
      inner ℂ (dilationCoefficients a b W x) (dilationCoefficients a b W y) := by
  simp only [dilationCoefficients, Module.Basis.constr_apply_fintype,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  simp only [dilation_coefficient_gram V W hVW]

/-- Supplied (possibly nonminimal) dilations of the same channel can be
aligned by an environmental contraction.  No isometry, full-rank, or
nondegeneracy assumption is needed. -/
theorem exists_dilation_alignment
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (hVW : dilationChannel V = dilationChannel W) :
    ∃ U : E →ₗ[ℂ] F, (LinearMap.adjoint U).comp U ≤ 1 ∧
      (environmentMap (B := B) U).comp V = W := by
  let a := stdOrthonormalBasis ℂ A
  let b := stdOrthonormalBasis ℂ B
  obtain ⟨U, hU, hfactor⟩ := exists_contraction_factor
    (dilationCoefficients a b W) (dilationCoefficients a b V) (by
      intro x
      have h := congrArg RCLike.re (dilationCoefficients_inner a b V W hVW x x)
      simp only [inner_self_eq_norm_sq (𝕜 := ℂ)] at h
      nlinarith [norm_nonneg (dilationCoefficients a b V x),
        norm_nonneg (dilationCoefficients a b W x)])
  refine ⟨U, hU, ?_⟩
  apply a.toBasis.ext
  intro i
  apply outputSlice_ext b
  intro j
  have h := congrArg (fun L : A ⊗[ℂ] B →ₗ[ℂ] F => L (a i ⊗ₜ[ℂ] b j)) hfactor
  simp only [LinearMap.comp_apply, dilationCoefficients_basis] at h
  simpa only [LinearMap.comp_apply, outputSlice_environmentMap] using h.symm

/-- Gour's decomposition can be transferred to any prescribed dilation,
without changing the output CP bound or the error constant.  The construction
of the initial two-piece decomposition is a separate theorem. -/
theorem fixed_dilation_filter_of_decomposition
    (V : A →ₗ[ℂ] B ⊗[ℂ] F) (X Y : A →ₗ[ℂ] B ⊗[ℂ] E)
    (Λ : QuantumChannel.T A B) (ε : ℝ)
    (hV : dilationChannel (X + Y) = dilationChannel V)
    (hX : CPLe (dilationChannel X) Λ) (hY : ‖Y.toContinuousLinearMap‖ ≤ ε) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] F,
      CPLe (dilationChannel W) Λ ∧ ‖(V - W).toContinuousLinearMap‖ ≤ ε := by
  obtain ⟨U, hU, hUV⟩ := exists_dilation_alignment (X + Y) V hV
  exact fixed_environment_filter U V X Y Λ ε hU hUV hX hY

theorem dilation_coefficient_gram_add {G : Type u} [Qudit G]
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (R : A →ₗ[ℂ] B ⊗[ℂ] G)
    (hV : dilationChannel V = dilationChannel W + dilationChannel R)
    (a c : A) (b d : B) :
    inner ℂ (outputSlice b (V a)) (outputSlice d (V c)) =
      inner ℂ (outputSlice b (W a)) (outputSlice d (W c)) +
      inner ℂ (outputSlice b (R a)) (outputSlice d (R c)) := by
  rw [inner_outputSlice, inner_outputSlice, inner_outputSlice]
  have h := congrArg (fun Φ : QuantumChannel.T A B => Φ (outer_product a c)) hV
  change dilationChannel V (outer_product a c) =
    dilationChannel W (outer_product a c) + dilationChannel R (outer_product a c) at h
  simp only [dilationChannel_outer_product] at h
  rw [h, LinearMap.add_apply, inner_add_right]

theorem dilationCoefficients_inner_add {ι κ : Type*} {G : Type u}
    [Fintype ι] [Fintype κ] [Qudit G]
    (a : OrthonormalBasis ι ℂ A) (b : OrthonormalBasis κ ℂ B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (R : A →ₗ[ℂ] B ⊗[ℂ] G)
    (hV : dilationChannel V = dilationChannel W + dilationChannel R)
    (x y : A ⊗[ℂ] B) :
    inner ℂ (dilationCoefficients a b V x) (dilationCoefficients a b V y) =
      inner ℂ (dilationCoefficients a b W x) (dilationCoefficients a b W y) +
      inner ℂ (dilationCoefficients a b R x) (dilationCoefficients a b R y) := by
  simp only [dilationCoefficients, Module.Basis.constr_apply_fintype,
    inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    dilation_coefficient_gram_add V W R hV, mul_add, Finset.sum_add_distrib]

/-- Complete-positive order gives an environmental contraction between any
two supplied dilations.  This is the finite-dimensional CP Radon–Nikodym
factorization in the form used by the filter construction. -/
theorem exists_ordered_dilation_factor
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (W : A →ₗ[ℂ] B ⊗[ℂ] F)
    (hVW : CPLe (dilationChannel V) (dilationChannel W)) :
    ∃ U : F →ₗ[ℂ] E, (LinearMap.adjoint U).comp U ≤ 1 ∧
      (environmentMap (B := B) U).comp W = V := by
  let a := stdOrthonormalBasis ℂ A
  let b := stdOrthonormalBasis ℂ B
  obtain ⟨G, instG, hrep⟩ := cp_to_stinespring a.toBasis
    (dilationChannel W - dilationChannel V) hVW
  letI := instG
  obtain ⟨R, hR⟩ := hrep
  have hR' : dilationChannel R = dilationChannel W - dilationChannel V := by
    ext1 X
    exact (hR X).symm
  have hsum : dilationChannel W = dilationChannel V + dilationChannel R := by
    rw [hR']
    abel
  obtain ⟨U, hU, hfactor⟩ := exists_contraction_factor
    (dilationCoefficients a b V) (dilationCoefficients a b W) (by
      intro x
      have h := congrArg RCLike.re
        (dilationCoefficients_inner_add a b W V R hsum x x)
      simp only [map_add, inner_self_eq_norm_sq (𝕜 := ℂ)] at h
      nlinarith [sq_nonneg ‖dilationCoefficients a b R x‖,
        norm_nonneg (dilationCoefficients a b V x),
        norm_nonneg (dilationCoefficients a b W x)])
  refine ⟨U, hU, ?_⟩
  apply a.toBasis.ext
  intro i
  apply outputSlice_ext b
  intro j
  have h := congrArg (fun L : A ⊗[ℂ] B →ₗ[ℂ] E => L (a i ⊗ₜ[ℂ] b j)) hfactor
  simp only [LinearMap.comp_apply, dilationCoefficients_basis] at h
  simpa only [LinearMap.comp_apply, outputSlice_environmentMap] using h.symm

end QuantumChannelContinuity
