import QuantumChannelContinuity.DivergenceSchatten

/-!
# Complex trace Hölder

The bound is proved from Hilbert–Schmidt Cauchy–Schwarz and the already
proved positive-operator trace Hölder inequality. Positive regularization
handles all singular operators.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder MatrixOrder NNReal Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {H : Type u} [Qudit H]

/-- Hilbert–Schmidt coordinates represent the full complex trace pairing. -/
theorem coefficientVector_inner (A B : L H) :
    inner ℂ (coefficientVector A) (coefficientVector B) = Tr (star A * B) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ H)]
  simp only [coefficientVector, PiLp.inner_apply,
    LinearMap.star_eq_adjoint, Module.End.mul_apply, LinearMap.adjoint_inner_right]

theorem complex_trace_hilbertSchmidt (A B : L H) :
    ‖Tr (star A * B)‖ ≤ Real.sqrt (Tr (A * star A)).re * Real.sqrt (Tr (B * star B)).re := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (coefficientVector A) (coefficientVector B)
  rw [coefficientVector_inner] at h
  have hn (C : L H) : Real.sqrt (Tr (C * star C)).re = ‖coefficientVector C‖ := by
    change Real.sqrt (Tr (coefficientDensity C)).re = _
    rw [← coefficientVector_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn] using h

/-- Matrix coordinates commute with every real CFC power on a finite spectrum. -/
theorem toMatrixOrthonormal_rpow_all
    (b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H) (X : L H)
    (hX : X.IsPositive) (t : ℝ) :
    LinearMap.toMatrixOrthonormal b (CFC.rpow X t) =
      CFC.rpow (LinearMap.toMatrixOrthonormal b X) t := by
  have hX0 : 0 ≤ X := (LinearMap.nonneg_iff_isPositive _).2 hX
  have hφ : Continuous (LinearMap.toMatrixOrthonormal b) :=
    (StarAlgEquiv.isometry (LinearMap.toMatrixOrthonormal b)).continuous
  have hφ0 : 0 ≤ LinearMap.toMatrixOrthonormal b X :=
    map_nonneg (LinearMap.toMatrixOrthonormal b) hX0
  have hf : ContinuousOn (fun x : ℝ => x ^ t) (spectrum ℝ X) :=
    (finite_real_operator_spectrum X).continuousOn _
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_pow,
    CFC.rpow_eq_cfc_real (ha := hX0), CFC.rpow_eq_cfc_real (ha := hφ0)]
  simpa using (StarAlgHomClass.map_cfc (R := ℝ) (φ := LinearMap.toMatrixOrthonormal b)
    (f := fun x : ℝ => x ^ t) (a := X) (hf := hf) (hφ := hφ)
    (ha := hX.isSelfAdjoint) (hφa := hX.isSelfAdjoint.map (LinearMap.toMatrixOrthonormal b)))

/-- Left and right Gram operators have identical real-power traces, including
singular operators and arbitrary real exponents. -/
theorem trace_rpow_star_mul_swap (A : L H) (t : ℝ) :
    Tr (CFC.rpow (star A * A) t) = Tr (CFC.rpow (A * star A) t) := by
  let b := stdOrthonormalBasis ℂ H
  let M := LinearMap.toMatrixOrthonormal b A
  have h₁ : (star M * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have h₂ : (M * star M).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self M
  have heig : h₁.eigenvalues = h₂.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    exact Matrix.charpoly_mul_comm (star M) M
  have hp₁ : (star A * A).IsPositive := (LinearMap.nonneg_iff_isPositive _).1 (star_mul_self_nonneg A)
  have hp₂ : (A * star A).IsPositive := (LinearMap.nonneg_iff_isPositive _).1 (mul_star_self_nonneg A)
  rw [tr_eq_matrix_trace_orthonormal b, toMatrixOrthonormal_rpow_all b _ hp₁ t,
    tr_eq_matrix_trace_orthonormal b (CFC.rpow (A * star A) t),
    toMatrixOrthonormal_rpow_all b _ hp₂ t]
  simp only [map_mul, map_star]
  change Matrix.trace (CFC.rpow (star M * M) t) = Matrix.trace (CFC.rpow (M * star M) t)
  rw [matrix_trace_rpow_eq_sum_eigenvalues _ h₁ (Matrix.posSemidef_conjTranspose_mul_self M).nonneg,
    matrix_trace_rpow_eq_sum_eigenvalues _ h₂ (Matrix.posSemidef_self_mul_conjTranspose M).nonneg, heig]

/-- Positive powers vary continuously over the entire nonnegative cone. -/
theorem operator_rpow_continuousOn_nonneg [Nontrivial H] {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun X : L H => CFC.rpow X t) {X : L H | 0 ≤ X} := by
  have hmem : (Set.univ : Set ℝ≥0) ∈ 𝓝ˢ (⋃ X ∈ {X : L H | 0 ≤ X}, spectrum ℝ≥0 X) :=
    Filter.univ_mem
  exact (continuousOn_id : ContinuousOn (fun X : L H => X) {X : L H | 0 ≤ X}).cfc_nnreal_of_mem_nhdsSet
    (s := Set.univ) (f := (· ^ t)) hmem (ha' := fun X hX => hX)
    (hf := NNReal.continuousOn_rpow_const (.inr ht))

private theorem holder_weight_sqrt {p q R S : ℝ} (hpq : p.HolderConjugate q)
    (hp2 : p < 2) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Real.sqrt R * Real.sqrt (R ^ ((2 - p) / p) * S ^ (2 / q)) =
      R ^ (1 / p) * S ^ (1 / q) := by
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have h2p : 0 ≤ 2 - p := by linarith
  rw [Real.sqrt_mul (Real.rpow_nonneg hR _), Real.sqrt_eq_rpow,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hR, ← Real.rpow_mul hS, ← mul_assoc,
    ← Real.rpow_add_of_nonneg hR (by positivity) (by positivity)]
  congr 1
  · congr 1
    field_simp
    ring
  · congr 1
    ring

/-- Weighted Hilbert–Schmidt proves Hölder below exponent two with any
positive-definite majorant of the left Gram operator. -/
theorem complex_trace_holder_majorant [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (A B X : L H)
    (hX : X ∈ pdSetLM) (hAX : A * star A ≤ X) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow X (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have hp := hpq.lt
  have hp0 := hpq.pos
  have hq0 := hpq.symm.pos
  have h2p : 0 < 2 - p := by linarith
  have hX0 := nonneg_of_pdSetLM hX
  have hXp := (LinearMap.nonneg_iff_isPositive _).1 hX0
  have hXu := isUnit_of_pdSetLM hX
  let a := (p - 2) / 4
  let S := CFC.rpow X a
  let T := CFC.rpow X (-a)
  let C := S * A
  let D := T * B
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hT : T.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hSstar : star S = S := hS.isSelfAdjoint.star_eq
  have hTstar : star T = T := hT.isSelfAdjoint.star_eq
  have hST : S * T = 1 := by
    change X ^ a * X ^ (-a) = 1
    rw [← CFC.rpow_add hXu, add_neg_cancel, CFC.rpow_zero X hX0]
  have hpair : star C * D = star A * B := by
    dsimp [C, D]
    rw [star_mul, hSstar]
    calc
      star A * S * (T * B) = star A * (S * T) * B := by noncomm_ring
      _ = star A * B := by rw [hST, mul_one]
  have hSX : S * X * S = CFC.rpow X (p / 2) := by
    change CFC.rpow X a * X * CFC.rpow X a = _
    conv_lhs => arg 1; arg 2; rw [← CFC.rpow_one X hX0]
    change CFC.rpow X a * CFC.rpow X 1 * CFC.rpow X a = _
    rw [operator_rpow_mul X hXp a 1 (by dsimp [a]; linarith : a + 1 ≠ 0),
      operator_rpow_mul X hXp (a + 1) a (by dsimp [a]; linarith : a + 1 + a ≠ 0)]
    congr 1
    dsimp [a]
    ring
  have hCeq : C * star C = S * (A * star A) * S := by
    simp only [C, star_mul, hSstar]
    noncomm_ring
  have hCbound : (Tr (C * star C)).re ≤ (Tr (CFC.rpow X (p / 2))).re := by
    have h := trace_mul_re_mono (hS.isSelfAdjoint.conjugate_le_conjugate hAX)
      (1 : L H) LinearMap.isPositive_one
    simpa only [mul_one, ← hCeq, hSX] using h
  have hTT : T * T = CFC.rpow X ((2 - p) / 2) := by
    change CFC.rpow X (-a) * CFC.rpow X (-a) = _
    rw [operator_rpow_mul X hXp (-a) (-a) (by dsimp [a]; linarith : -a + -a ≠ 0)]
    congr 1
    dsimp [a]
    ring
  have hDtrace : Tr (D * star D) = Tr (CFC.rpow X ((2 - p) / 2) * (B * star B)) := by
    have heq : D * star D = (T * (B * star B)) * T := by
      simp only [D, star_mul, hTstar]
      noncomm_ring
    rw [heq, LinearMap.trace_mul_comm ℂ (T * (B * star B)) T, ← mul_assoc, hTT]
  have hrs : (p / (2 - p)).HolderConjugate (q / 2) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · apply (lt_div_iff₀ h2p).2
      linarith
    · have hh := hpq.inv_add_inv_eq_one
      field_simp at hh ⊢
      nlinarith [hpq.mul_eq_add]
  have hD := trace_holder hrs (CFC.rpow X ((2 - p) / 2)) (B * star B)
    ((LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg)
    ((LinearMap.nonneg_iff_isPositive _).1 (mul_star_self_nonneg B))
  have hpow : CFC.rpow (CFC.rpow X ((2 - p) / 2)) (p / (2 - p)) = CFC.rpow X (p / 2) := by
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X ((2 - p) / 2) (p / (2 - p))
      (by positivity) (by positivity) hX0]
    congr 1
    field_simp
  rw [hpow] at hD
  have hr : 1 / (p / (2 - p)) = (2 - p) / p := by field_simp
  have hs : 1 / (q / 2) = 2 / q := by field_simp
  rw [hr, hs] at hD
  have h := complex_trace_hilbertSchmidt C D
  rw [hpair, hDtrace] at h
  refine h.trans ((mul_le_mul (Real.sqrt_le_sqrt hCbound) (Real.sqrt_le_sqrt hD)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq ?_)
  exact holder_weight_sqrt hpq hp2 (trace_rpow_re_nonneg X (p / 2))
    (trace_rpow_re_nonneg (B * star B) (q / 2))

/-- Removing the strictly positive majorant by positive regularization. -/
theorem complex_trace_holder_lt_two [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (A B : L H) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have hp0 := hpq.pos
  let X : ℝ → L H := fun ε => A * star A + (ε : ℂ) • 1
  have hXpd (ε : ℝ) (hε : 0 < ε) : X ε ∈ pdSetLM :=
    pdSetLM_add_nonneg (mul_star_self_nonneg A) (pos_smul_one_pdSetLM hε)
  have hAX (ε : ℝ) (hε : 0 < ε) : A * star A ≤ X ε := by
    exact le_add_of_nonneg_right (smul_nonneg (by exact_mod_cast hε.le : (0 : ℂ) ≤ ε) zero_le_one)
  have hXlim : Filter.Tendsto X (𝓝[>] (0 : ℝ)) (𝓝 (A * star A)) := by
    have hc : Continuous X := by dsimp [X]; fun_prop
    simpa [X] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hwithin : Filter.Tendsto X (𝓝[>] (0 : ℝ)) (𝓝[{Y : L H | 0 ≤ Y}] (A * star A)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hXlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact nonneg_of_pdSetLM (hXpd ε hε)
  have hpow := ((operator_rpow_continuousOn_nonneg (H := H)
    (show 0 ≤ p / 2 by positivity)) (A * star A) (mul_star_self_nonneg A)).tendsto.comp hwithin
  have htrace := Complex.continuous_re.continuousAt.tendsto.comp
    (((LinearMap.trace ℂ H).continuous_of_finiteDimensional.tendsto _).comp hpow)
  have hr := ((Real.continuousAt_rpow_const _ (1 / p) (Or.inr (by positivity))).tendsto.comp htrace).mul_const
    ((Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hr
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact complex_trace_holder_majorant hpq hp2 A B (X ε) (hXpd ε hε) (hAX ε hε)

/-- Complex trace Hölder for arbitrary operators with conjugate exponents.
No support, invertibility, or positivity assumptions on the operators occur. -/
theorem complex_trace_holder_adjoint [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (A B : L H) :
    ‖Tr (star A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  rcases lt_trichotomy p 2 with hp | hp | hp
  · exact complex_trace_holder_lt_two hpq hp A B
  · have hq : q = 2 := by rw [hpq.conjugate_eq, hp]; norm_num
    subst p
    subst q
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), CFC.rpow_eq_pow,
      CFC.rpow_one _ (mul_star_self_nonneg A), CFC.rpow_one _ (mul_star_self_nonneg B),
      Real.sqrt_eq_rpow] using complex_trace_hilbertSchmidt A B
  · have hq : q < 2 := by
      rw [hpq.conjugate_eq]
      apply (div_lt_iff₀ hpq.sub_one_pos).2
      linarith
    have h := complex_trace_holder_lt_two hpq.symm hq B A
    have hsymm : ‖Tr (star B * A)‖ = ‖Tr (star A * B)‖ := by
      rw [← coefficientVector_inner, ← coefficientVector_inner]
      exact norm_inner_symm _ _
    simpa only [hsymm, mul_comm] using h

/-- The equivalent non-adjoint trace form, with left Gram operators in both
Schatten factors. -/
theorem complex_trace_holder [Nontrivial H] {p q : ℝ}
    (hpq : p.HolderConjugate q) (A B : L H) :
    ‖Tr (A * B)‖ ≤ (Tr (CFC.rpow (A * star A) (p / 2))).re ^ (1 / p) *
      (Tr (CFC.rpow (B * star B) (q / 2))).re ^ (1 / q) := by
  have h := complex_trace_holder_adjoint hpq (star A) B
  simpa only [star_star, trace_rpow_star_mul_swap] using h

end QuantumChannelContinuity
