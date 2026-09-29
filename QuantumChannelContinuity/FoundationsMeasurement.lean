import QuantumChannelContinuity.Foundations

/-!
# Measurement channels built from positive operator-valued measures

This constructs the measurement CPTP map itself, from positive effects summing
to the identity, and proves that its diagonal entries are Born probabilities.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {H : Type} [Qudit H] [Nontrivial H]

omit [Nontrivial H] in
private lemma outer_apply {K : Type} [Qudit K] (u : H) (v : K) (x : H) :
    outer_product u v x = inner ℂ u x • v := by
  simp [outer_product_eq_rankOne]

omit [Nontrivial H] in
private lemma outer_adjoint {K : Type} [Qudit K] (u : H) (v : K) :
    LinearMap.adjoint (outer_product u v) = outer_product v u := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [LinearMap.adjoint_inner_left, outer_apply, outer_apply,
    inner_smul_right, inner_smul_left, inner_conj_symm]
  ring

omit [Nontrivial H] in
private lemma kraus_outer {K : Type} [Qudit K] (u : H) (v : K) (γ : L H) :
    krausTerm (outer_product u v) γ = inner ℂ u (γ u) • outer_product v v := by
  ext x
  change (outer_product u v) (γ ((LinearMap.adjoint (outer_product u v)) x)) = _
  rw [outer_adjoint]
  simp only [outer_apply, map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  ring

/-- The linear map for one measurement outcome, with its classical output
encoded by a unit vector `e`. -/
noncomputable def measurementTerm {K : Type} [Qudit K] (M : L H) (e : K) : T H K where
  toFun γ := Tr (M * γ) • outer_product e e
  map_add' γ δ := by simp [mul_add, add_smul]
  map_smul' c γ := by simp [smul_smul]

/-- A square-root Kraus decomposition of one positive measurement effect. -/
theorem measurementTerm_kraus {K : Type} [Qudit K]
    (M : L H) (hM : 0 ≤ M) (e : K) :
    measurementTerm M e = ∑ j : Fin (Module.finrank ℂ H),
      krausTerm (outer_product (CFC.sqrt M ((stdOrthonormalBasis ℂ H) j)) e) := by
  classical
  let b := stdOrthonormalBasis ℂ H
  let S := CFC.sqrt M
  have hadj : LinearMap.adjoint S = S := by
    rw [← LinearMap.star_eq_adjoint]
    exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg M)).star_eq
  apply LinearMap.ext
  intro γ
  rw [LinearMap.sum_apply]
  simp_rw [kraus_outer]
  change Tr (M * γ) • outer_product e e =
    ∑ j, inner ℂ (S (b j)) (γ (S (b j))) • outer_product e e
  rw [← Finset.sum_smul]
  congr 1
  have hinner : ∀ j, inner ℂ (S (b j)) (γ (S (b j))) =
      inner ℂ (b j) ((S * γ * S) (b j)) := by
    intro j
    simpa only [hadj, Module.End.mul_apply] using
      (LinearMap.adjoint_inner_right S (b j) (γ (S (b j)))).symm
  simp_rw [hinner]
  rw [← LinearMap.trace_eq_sum_inner (T := S * γ * S) b]
  have hcycle : Tr (S * γ * S) = Tr (S * (S * γ)) :=
    LinearMap.trace_comp_comm' S (S * γ)
  rw [hcycle, ← mul_assoc, CFC.sqrt_mul_sqrt_self M hM]

/-- Positive measurement effects give completely positive outcome maps. -/
theorem measurementTerm_completelyPositive {K : Type} [Qudit K]
    (M : L H) (hM : 0 ≤ M) (e : K) : IsCompletelyPositive (measurementTerm M e) := by
  rw [measurementTerm_kraus M hM e]
  exact sum_krausTerm_isCompletelyPositive _

/-- A finite positive operator-valued measure. -/
structure POVM (H : Type) [Qudit H] (ι : Type) [Fintype ι] where
  effect : ι → L H
  nonneg : ∀ i, 0 ≤ effect i
  sum_one : ∑ i, effect i = 1

namespace POVM

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The measurement superoperator, in a classical orthonormal output basis. -/
noncomputable def linearMap (M : POVM H ι) : T H (EuclideanSpace ℂ ι) :=
  ∑ i, measurementTerm (M.effect i) ((EuclideanSpace.basisFun ι ℂ) i)

theorem linearMap_apply (M : POVM H ι) (γ : L H) :
    M.linearMap γ = ∑ i, Tr (M.effect i * γ) •
      outer_product ((EuclideanSpace.basisFun ι ℂ) i) ((EuclideanSpace.basisFun ι ℂ) i) := by
  simp [linearMap, measurementTerm, LinearMap.sum_apply]

theorem linearMap_completelyPositive (M : POVM H ι) : IsCompletelyPositive M.linearMap := by
  have hrep : M.linearMap = ∑ ij : ι × Fin (Module.finrank ℂ H),
      krausTerm (outer_product (CFC.sqrt (M.effect ij.1) ((stdOrthonormalBasis ℂ H) ij.2))
        ((EuclideanSpace.basisFun ι ℂ) ij.1)) := by
    rw [Fintype.sum_prod_type]
    unfold linearMap
    apply Finset.sum_congr rfl
    intro i _
    exact measurementTerm_kraus (M.effect i) (M.nonneg i) _
  rw [hrep]
  exact sum_krausTerm_isCompletelyPositive _

theorem linearMap_trace (M : POVM H ι) (γ : L H) : Tr (M.linearMap γ) = Tr γ := by
  rw [linearMap_apply, map_sum]
  simp only [map_smul, smul_eq_mul, trace_outer_product_basisFun, ↓reduceIte, mul_one]
  rw [← map_sum, ← Finset.sum_mul, M.sum_one, one_mul]

/-- The POVM defines a CPTP channel; complete positivity is proved from the
square-root Kraus decomposition, rather than added as an assumption. -/
noncomputable def channel (M : POVM H ι) : CPTP H (EuclideanSpace ℂ ι) where
  toFun := M.linearMap
  map_add' := M.linearMap.map_add
  map_smul' := M.linearMap.map_smul
  map_cstarMatrix_nonneg' k X hX := by
    obtain ⟨Φ, hΦ⟩ := M.linearMap_completelyPositive
    have h := Φ.map_cstarMatrix_nonneg' k X hX
    rw [hΦ] at h
    exact h
  trace_map γ := (M.linearMap_trace γ).symm

/-- The diagonal measurement output equals the Born probability of its effect. -/
theorem channel_apply_basis (M : POVM H ι) (γ : L H) (j : ι) :
    M.channel.toFun γ ((EuclideanSpace.basisFun ι ℂ) j) =
      Tr (M.effect j * γ) • ((EuclideanSpace.basisFun ι ℂ) j) := by
  change M.linearMap γ ((EuclideanSpace.basisFun ι ℂ) j) = _
  rw [linearMap_apply, LinearMap.sum_apply]
  simp [outer_product_eq_rankOne, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- The probability of an outcome of this concrete POVM. -/
noncomputable def probability (M : POVM H ι) (ρ : DensityState H) (i : ι) : ℝ :=
  (Tr (M.effect i * ρ.op)).re

theorem trace_effect_nonneg (M : POVM H ι) (ρ : DensityState H) (i : ι) :
    (0 : ℂ) ≤ Tr (M.effect i * ρ.op) := by
  have hpos := (LinearMap.nonneg_iff_isPositive _).mp (ρ.map M.channel).nonneg
  have h := hpos.inner_nonneg_right ((EuclideanSpace.basisFun ι ℂ) i)
  change 0 ≤ inner ℂ _ (M.channel.toFun ρ.op _) at h
  rw [M.channel_apply_basis, inner_smul_right,
    (EuclideanSpace.basisFun ι ℂ).inner_eq_one, mul_one] at h
  exact h

theorem probability_nonneg (M : POVM H ι) (ρ : DensityState H) (i : ι) :
    0 ≤ M.probability ρ i := (M.trace_effect_nonneg ρ i).1

theorem sum_probability (M : POVM H ι) (ρ : DensityState H) :
    ∑ i, M.probability ρ i = 1 := by
  unfold probability
  rw [← Complex.re_sum, ← map_sum, ← Finset.sum_mul, M.sum_one, one_mul, ρ.trace_one]
  rfl

theorem probability_le_one (M : POVM H ι) (ρ : DensityState H) (i : ι) :
    M.probability ρ i ≤ 1 := by
  rw [← M.sum_probability ρ]
  exact Finset.single_le_sum (fun j _ => M.probability_nonneg ρ j) (Finset.mem_univ i)

/-- The output is diagonal with real eigenvalues equal to the probabilities. -/
theorem channel_apply_basis_probability (M : POVM H ι) (ρ : DensityState H) (i : ι) :
    M.channel.toFun ρ.op ((EuclideanSpace.basisFun ι ℂ) i) =
      (M.probability ρ i : ℂ) • ((EuclideanSpace.basisFun ι ℂ) i) := by
  rw [M.channel_apply_basis, Complex.eq_re_of_ofReal_le (M.trace_effect_nonneg ρ i)]
  rfl

end POVM

/-- The two-outcome POVM associated with an arbitrary quantum effect. -/
noncomputable def binaryPOVM (M : L H) (hM : 0 ≤ M) (hM1 : M ≤ 1) : POVM H (Fin 2) where
  effect i := if i = 0 then M else 1 - M
  nonneg i := by split_ifs; exact hM; exact sub_nonneg.mpr hM1
  sum_one := by simp [Fin.sum_univ_two]

/-- Rényi data processing for an arbitrary concrete two-outcome quantum test. -/
theorem binaryRenyi_dataProcessing (M : L H) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    {α : ℝ} (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1) (ρ σ : DensityState H) :
    stateRenyi α (ρ.map (binaryPOVM M hM hM1).channel)
      (σ.map (binaryPOVM M hM hM1).channel) ≤ stateRenyi α ρ σ :=
  stateRenyi_dataProcessing _ hα hα1 ρ σ

/-- Umegaki data processing for an arbitrary concrete two-outcome quantum test. -/
theorem binaryRelative_dataProcessing (M : L H) (hM : 0 ≤ M) (hM1 : M ≤ 1)
    (ρ σ : DensityState H) :
    stateRelative (ρ.map (binaryPOVM M hM hM1).channel)
      (σ.map (binaryPOVM M hM hM1).channel) ≤ stateRelative ρ σ :=
  stateRelative_dataProcessing _ ρ σ

end QuantumChannelContinuity
