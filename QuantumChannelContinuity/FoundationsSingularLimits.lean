import QuantumChannelContinuity.FoundationsDiagonal

/-!
# Order-one continuity for singular states with a common eigenbasis

Zero eigenvalues are retained. Only the support inclusion is required; neither
state is assumed positive definite. General noncommuting singular states are
not covered by this result.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

private theorem scalar_sandwiched_exp {α p q : ℝ}
    (hα : 0 < α) (hp : 0 < p) (hq : 0 < q) :
    (q ^ ((1 - α) / (2 * α)) * p * q ^ ((1 - α) / (2 * α))) ^ α =
      p * Real.exp ((α - 1) * (Real.log p - Real.log q)) := by
  have hqpow : 0 < q ^ ((1 - α) / (2 * α)) := Real.rpow_pos_of_pos hq _
  rw [Real.rpow_def_of_pos (mul_pos (mul_pos hqpow hp) hqpow),
    Real.log_mul (ne_of_gt (mul_pos hqpow hp)) hqpow.ne',
    Real.log_mul hqpow.ne' hp.ne', Real.log_rpow hq]
  have heq : (((1 - α) / (2 * α) * Real.log q + Real.log p) +
      (1 - α) / (2 * α) * Real.log q) * α =
      Real.log p + (α - 1) * (Real.log p - Real.log q) := by
    field_simp [hα.ne']
    ring
  rw [heq, Real.exp_add, Real.exp_log hp]

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Positivity forces real eigenvalues on a normalized eigenvector to be
nonnegative. -/
theorem eigenvalue_nonneg {A : L H} (hA : 0 ≤ A) {v : H}
    (hv : inner ℂ v v = 1) {r : ℝ} (he : A v = (r : ℂ) • v) : 0 ≤ r := by
  have h := ((LinearMap.nonneg_iff_isPositive _).mp hA).inner_nonneg_right v
  rw [he, inner_smul_right, hv, mul_one] at h
  exact_mod_cast h

/-- The derivative at order one of the actual quantum quasi-entropy, allowing
zero eigenvalues, on the common-eigenbasis support domain. -/
theorem hasDerivAt_quasi_one_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : DensityState H)
    (p q : ι → ℝ) (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) (hs : suppLE ρ.op σ.op) :
    HasDerivAt (fun α => (sandwichedQuasi α ρ.op σ.op).re)
      (∑ i, p i * (Real.log (p i) - Real.log (q i))) 1 := by
  let F : ℝ → ℝ := fun α => ∑ i, p i * Real.exp ((α - 1) * (Real.log (p i) - Real.log (q i)))
  have hF : HasDerivAt F (∑ i, p i * (Real.log (p i) - Real.log (q i))) 1 := by
    apply HasDerivAt.fun_sum
    intro i _
    have h := ((((hasDerivAt_id (1 : ℝ)).sub_const 1).mul_const
      (Real.log (p i) - Real.log (q i))).exp).const_mul (p i)
    simpa using h
  apply hF.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)] with α hα
  rw [sandwichedQuasi_common_eigenbasis b _ _ ρ.nonneg σ.nonneg p q hp hq α]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp0 : p i = 0
  · simp [hp0, Real.zero_rpow hα.ne']
  · have hpp : 0 < p i := lt_of_le_of_ne
      (eigenvalue_nonneg ρ.nonneg (b.inner_eq_one i) (hp i)) (Ne.symm hp0)
    have hq0 : q i ≠ 0 := by
      intro hz
      exact hp0 (zero_of_support_common_eigenvector hs (b.orthonormal.ne_zero i) (hp i) (hq i) hz)
    have hqp : 0 < q i := lt_of_le_of_ne
      (eigenvalue_nonneg σ.nonneg (b.inner_eq_one i) (hq i)) (Ne.symm hq0)
    exact scalar_sandwiched_exp hα hpp hqp

/-- The two-sided order-one limit holds for common-eigenbasis states on the
support domain, even when one or both density operators are singular. -/
theorem stateRenyi_tendsto_one_common_eigenbasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : DensityState H)
    (p q : ι → ℝ) (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) (hs : suppLE ρ.op σ.op) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[≠] (1 : ℝ)) (𝓝 (stateRelative ρ σ)) := by
  let E := ∑ i, p i * (Real.log (p i) - Real.log (q i))
  have hQ1 : (sandwichedQuasi 1 ρ.op σ.op).re = 1 := by
    rw [sandwichedQuasi_one_re ρ.op σ.op σ.nonneg ρ.nonneg, ρ.trace_one]
    rfl
  have hdQ := hasDerivAt_quasi_one_common_eigenbasis b ρ σ p q hp hq hs
  have hdlog : HasDerivAt (fun α => Real.log ((sandwichedQuasi α ρ.op σ.op).re)) E 1 := by
    simpa [hQ1, E] using hdQ.log (by rw [hQ1]; norm_num)
  rw [hasDerivAt_iff_tendsto_slope] at hdlog
  have hreal : Tendsto (fun α => sandwichedRenyiDiv α ρ.op σ.op)
      (𝓝[≠] (1 : ℝ)) (𝓝 E) := by
    apply hdlog.congr'
    filter_upwards [] with α
    rw [slope_def_field]
    simp [sandwichedRenyiDiv, hQ1, ρ.trace_one, div_eq_mul_inv, mul_comm]
  have hcoe := (continuous_coe_real_ereal.tendsto (E / Real.log 2)).comp
    (hreal.div_const (Real.log 2))
  rw [umegaki_common_eigenbasis b ρ σ p q hp hq hs]
  apply hcoe.congr'
  have hQne : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), (sandwichedQuasi α ρ.op σ.op).re ≠ 0 :=
    (hdQ.continuousAt.eventually_ne (by rw [hQ1]; norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hQne] with α hα
  simp [stateRenyi, sandwichedRenyiDivNN, hs, hα]

/-- In particular, the left limit needed in the manuscript holds on this
singular common-eigenbasis domain. -/
theorem stateRenyi_tendsto_one_common_eigenbasis_left {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ H) (ρ σ : DensityState H)
    (p q : ι → ℝ) (hp : ∀ i, ρ.op (b i) = (p i : ℂ) • b i)
    (hq : ∀ i, σ.op (b i) = (q i : ℂ) • b i) (hs : suppLE ρ.op σ.op) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[<] (1 : ℝ)) (𝓝 (stateRelative ρ σ)) :=
  (stateRenyi_tendsto_one_common_eigenbasis b ρ σ p q hp hq hs).mono_left
    (nhdsWithin_mono _ (fun _ h => ne_of_lt h))

end QuantumChannelContinuity
