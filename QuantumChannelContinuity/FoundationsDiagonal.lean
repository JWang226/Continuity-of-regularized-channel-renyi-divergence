import QuantumChannelContinuity.FoundationsMeasurement

/-! # Evaluation of quantum divergences on measured, diagonal states -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Real operator powers act on an eigenvector by real scalar powers. -/
theorem rpow_apply_eigenvector {A : L H} (hA : 0 ≤ A) (t : ℝ)
    {v : H} (hv : v ≠ 0) {r : ℝ} (hr : A v = (r : ℂ) • v) :
    CFC.rpow A t v = ((r ^ t : ℝ) : ℂ) • v := by
  have hsa : IsSelfAdjoint A := (LinearMap.nonneg_iff_isPositive A).mp hA |>.isSelfAdjoint
  have heq : CFC.rpow A t = cfc (fun x : ℝ => x ^ t) A := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real (ha := hA)
  rw [heq]
  exact cfc_real_apply_eigenvector hsa (fun x => x ^ t) hr (mem_spectrum_real_of_eigenvector hv hr)

/-- Support inclusion forces every zero eigenvalue of the denominator to
have zero weight in the numerator in a common eigenbasis. -/
theorem zero_of_support_common_eigenvector {ρ σ : L H} (hs : suppLE ρ σ)
    {v : H} (hv : v ≠ 0) {p q : ℝ}
    (hp : ρ v = (p : ℂ) • v) (hq : σ v = (q : ℂ) • v) (hq0 : q = 0) : p = 0 := by
  have hvker : v ∈ LinearMap.ker σ := by
    rw [LinearMap.mem_ker, hq, hq0]
    simp
  have hz := LinearMap.mem_ker.mp (hs hvker)
  rw [hp] at hz
  have hp0 := (smul_eq_zero.mp hz).resolve_right hv
  exact_mod_cast hp0

/-- The sandwiched quantum trace evaluates to its classical sum on a shared
orthonormal eigenbasis, including zero eigenvalues. -/
theorem sandwichedQuasi_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : L H) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (p q : ι → ℝ) (hp : ∀ i, ρ (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ (b i) = (q i : ℂ) • b i) (α : ℝ) :
    (sandwichedQuasi α ρ σ).re =
      ∑ i, (q i ^ ((1 - α) / (2 * α)) * p i * q i ^ ((1 - α) / (2 * α))) ^ α := by
  let t := (1 - α) / (2 * α)
  let S := CFC.rpow σ t
  have hS : ∀ i, S (b i) = ((q i ^ t : ℝ) : ℂ) • b i := by
    intro i
    exact rpow_apply_eigenvector hσ t (b.orthonormal.ne_zero i) (hq i)
  have hM : 0 ≤ S * ρ * S := by
    exact conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hMeig : ∀ i, (S * ρ * S) (b i) =
      ((q i ^ t * p i * q i ^ t : ℝ) : ℂ) • b i := by
    intro i
    simp only [Module.End.mul_apply, hS, map_smul, hp, smul_smul]
    congr 1
    push_cast
    ring
  have hR : ∀ i, CFC.rpow (S * ρ * S) α (b i) =
      (((q i ^ t * p i * q i ^ t) ^ α : ℝ) : ℂ) • b i := by
    intro i
    exact rpow_apply_eigenvector hM α (b.orthonormal.ne_zero i) (hMeig i)
  change (Tr (CFC.rpow (S * ρ * S) α)).re = _
  rw [LinearMap.trace_eq_sum_inner (T := CFC.rpow (S * ρ * S) α) b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hR, inner_smul_right, b.inner_eq_one, mul_one, Complex.ofReal_re]

/-- Umegaki relative entropy is the classical diagonal log expression on a
common eigenbasis. The separate support-aware definition still assigns
infinity when the support condition fails. -/
theorem umegaki_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : DensityState H)
    (p q : ι → ℝ) (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i)
    (hs : suppLE ρ.op σ.op) :
    stateRelative ρ σ = ((∑ i, p i * (Real.log (p i) - Real.log (q i))) / Real.log 2 : ℝ) := by
  rw [stateRelative_eq_formula ρ σ hs]
  congr 2
  rw [LinearMap.trace_eq_sum_inner (T := ρ.op * (CFC.log ρ.op - CFC.log σ.op)) b,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hpLog : CFC.log ρ.op (b i) = (Real.log (p i) : ℂ) • b i :=
    cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg ρ.nonneg)
      Real.log (hp i) (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (hp i))
  have hqLog : CFC.log σ.op (b i) = (Real.log (q i) : ℂ) • b i :=
    cfc_real_apply_eigenvector (IsSelfAdjoint.of_nonneg σ.nonneg)
      Real.log (hq i) (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (hq i))
  change (inner ℂ (b i) (ρ.op ((CFC.log ρ.op - CFC.log σ.op) (b i)))).re = _
  simp only [LinearMap.sub_apply, hpLog, hqLog, map_sub, map_smul, hp,
    inner_sub_right, inner_smul_right, b.inner_eq_one, mul_one,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- Applying an arbitrary POVM makes the quantum sandwiched trace exactly the
classical expression in the actual Born probabilities. -/
theorem measured_sandwichedQuasi {H : Type} [Qudit H] [Nontrivial H]
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : POVM H ι) (ρ σ : DensityState H) (α : ℝ) :
    (sandwichedQuasi α (ρ.map M.channel).op (σ.map M.channel).op).re =
      ∑ i, (M.probability σ i ^ ((1 - α) / (2 * α)) * M.probability ρ i *
        M.probability σ i ^ ((1 - α) / (2 * α))) ^ α := by
  exact sandwichedQuasi_common_eigenbasis (EuclideanSpace.basisFun ι ℂ)
    _ _ (ρ.map M.channel).nonneg (σ.map M.channel).nonneg
    (M.probability ρ) (M.probability σ)
    (M.channel_apply_basis_probability ρ) (M.channel_apply_basis_probability σ) α

end QuantumChannelContinuity
