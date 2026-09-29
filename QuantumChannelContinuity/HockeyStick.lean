import QuantumChannelContinuity.Channels

/-!
# Quantum effects and hockey-stick divergence

These definitions are concrete variational testing quantities. They give
the unconditional bounds used by the threshold argument, including E ≤ 1.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {H K : Type u} [Qudit H] [Qudit K]

/-- An effect representing acceptance in a two-outcome quantum test. -/
structure Effect (H : Type u) [Qudit H] where
  op : L H
  nonneg : 0 ≤ op
  le_one : op ≤ 1

instance : Inhabited (Effect H) := ⟨⟨0, le_rfl, zero_le_one⟩⟩

@[simp] theorem Effect.default_op : (default : Effect H).op = 0 := rfl

/-- The trace of a product of positive operators is nonnegative, without
assuming the product itself is positive or that the operators commute. -/
theorem trace_product_nonneg {A B : L H} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (Tr (A * B)).re := by
  have hAp := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hBp := (LinearMap.nonneg_iff_isPositive B).mp hB
  rw [show A * B = A ∘ₗ B from rfl,
    trace_comp_eq_double_sum_eigen_overlap A B hAp hBp, Complex.re_sum]
  apply Finset.sum_nonneg
  intro j hj
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.re_sum]
  apply mul_nonneg (hBp.nonneg_eigenvalues (hn := rfl) j)
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hAp.nonneg_eigenvalues (hn := rfl) i) (Complex.normSq_nonneg _)

/-- The Born acceptance probability. -/
noncomputable def Effect.probability (T : Effect H) (ρ : DensityState H) : ℝ :=
  (Tr (T.op * ρ.op)).re

theorem Effect.probability_nonneg (T : Effect H) (ρ : DensityState H) :
    0 ≤ T.probability ρ := trace_product_nonneg T.nonneg ρ.nonneg

theorem Effect.probability_le_one (T : Effect H) (ρ : DensityState H) :
    T.probability ρ ≤ 1 := by
  have h := trace_product_nonneg (sub_nonneg.mpr T.le_one) ρ.nonneg
  simp only [sub_mul, one_mul, map_sub, ρ.trace_one, Complex.sub_re, Complex.one_re] at h
  exact sub_nonneg.mp h

/-- Variational state hockey-stick divergence. -/
noncomputable def stateHockey (γ : ℝ) (ρ σ : DensityState H) : ℝ :=
  sSup (Set.range (fun T : Effect H => T.probability ρ - γ * T.probability σ))

theorem hockey_objective_le_one {γ : ℝ} (hγ : 0 ≤ γ)
    (ρ σ : DensityState H) (T : Effect H) :
    T.probability ρ - γ * T.probability σ ≤ 1 := by
  have h := mul_nonneg hγ (T.probability_nonneg σ)
  linarith [T.probability_le_one ρ]

theorem stateHockey_le_one {γ : ℝ} (hγ : 0 ≤ γ) (ρ σ : DensityState H) :
    stateHockey γ ρ σ ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨T, rfl⟩
  exact hockey_objective_le_one hγ ρ σ T

theorem stateHockey_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (ρ σ : DensityState H) :
    0 ≤ stateHockey γ ρ σ := by
  have hb : BddAbove (Set.range (fun T : Effect H =>
      T.probability ρ - γ * T.probability σ)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨T, rfl⟩
    exact hockey_objective_le_one hγ ρ σ T
  have h := le_csSup hb (Set.mem_range_self (default : Effect H))
  simpa [stateHockey, Effect.probability] using h

variable [Nontrivial H] [Nontrivial K]

/-- The manuscript's stabilized channel hockey-stick divergence. -/
noncomputable def channelHockey (γ : ℝ) (N M : CPTP H K) : ℝ :=
  sSup (Set.range (fun ψ : PureInput (H ⊗[ℂ] H) =>
    stateHockey γ (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)))

omit [Nontrivial K] in
theorem channelHockey_le_one {γ : ℝ} (hγ : 0 ≤ γ) (N M : CPTP H K) :
    channelHockey γ N M ≤ 1 := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨ψ, rfl⟩
  exact stateHockey_le_one hγ _ _

omit [Nontrivial K] in
theorem channelHockey_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (N M : CPTP H K) :
    0 ≤ channelHockey γ N M := by
  let ψ : PureInput (H ⊗[ℂ] H) := Classical.choice inferInstance
  apply (stateHockey_nonneg hγ (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density)).trans
  unfold channelHockey
  apply le_csSup (s := Set.range (fun φ : PureInput (H ⊗[ℂ] H) =>
    stateHockey γ (amplifiedOutput N φ.density) (amplifiedOutput M φ.density)))
    _ (Set.mem_range_self ψ)
  refine ⟨1, ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact stateHockey_le_one hγ _ _

end QuantumChannelContinuity
