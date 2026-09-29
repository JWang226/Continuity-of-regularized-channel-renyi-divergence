import QuantumChannelContinuity.Foundations

/-!
# Two-sided order-one limit for faithful quantum states

The upstream derivative of the actual sandwiched quasi-entropy supplies a
punctured, two-sided limit. Both states are required to be positive definite;
this file does not claim the singular-state extension.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

variable {H : Type*} [Qudit H] [Nontrivial H]

omit [Nontrivial H] in
/-- The real-valued sandwiched divergence has a two-sided limit at one on the
faithful domain, proved from the derivative of its quasi-entropy. -/
theorem faithful_renyi_punctured_limit (ρ σ : DensityState H)
    (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    Tendsto (fun α => sandwichedRenyiDiv α ρ.op σ.op) (𝓝[≠] (1 : ℝ))
      (𝓝 (umegakiNorm ρ.op σ.op)) := by
  have hQ1 : (sandwichedQuasi 1 ρ.op σ.op).re = 1 := by
    rw [sandwichedQuasi_one_re ρ.op σ.op σ.nonneg ρ.nonneg, ρ.trace_one]
    rfl
  have hderiv := (hasDerivAt_sandwichedQuasi_re_one hρ hσ).log
    (by rw [hQ1]; norm_num : (sandwichedQuasi 1 ρ.op σ.op).re ≠ 0)
  have hd : HasDerivAt (fun α => Real.log ((sandwichedQuasi α ρ.op σ.op).re))
      (umegakiNorm ρ.op σ.op) 1 := by
    simpa [hQ1, umegakiNorm, ρ.trace_one] using hderiv
  rw [hasDerivAt_iff_tendsto_slope] at hd
  apply hd.congr'
  filter_upwards [] with α
  rw [slope_def_field]
  simp [sandwichedRenyiDiv, hQ1, ρ.trace_one, div_eq_mul_inv, mul_comm]

/-- The actual support-aware, base-two state divergence has the same
punctured limit for faithful states. -/
theorem stateRenyi_tendsto_one_faithful_twoSided (ρ σ : DensityState H)
    (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[≠] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) := by
  have hs := suppLE_of_pdSetLM_right ρ.op hσ
  have hlim := (faithful_renyi_punctured_limit ρ σ hρ hσ).div_const (Real.log 2)
  have hcoe := (continuous_coe_real_ereal.tendsto
    (umegakiNorm ρ.op σ.op / Real.log 2)).comp hlim
  have htarget : stateRelative ρ σ = (umegakiNorm ρ.op σ.op / Real.log 2 : ℝ) := by
    simp [stateRelative, umegakiRelEntropyNN, hs]
  rw [htarget]
  apply hcoe.congr'
  have hpos : ∀ᶠ α : ℝ in 𝓝[≠] (1 : ℝ), 0 < α :=
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos] with α hα
  have hQre := sandwichedQuasi_re_ne_zero_of_pdSetLM hα hρ hσ
  simp [stateRenyi, sandwichedRenyiDivNN, hs, hQre]

/-- The left limit needed by the optimization argument, on faithful states. -/
theorem stateRenyi_tendsto_one_faithful_left (ρ σ : DensityState H)
    (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    Tendsto (fun α => stateRenyi α ρ σ) (𝓝[<] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) :=
  (stateRenyi_tendsto_one_faithful_twoSided ρ σ hρ hσ).mono_left
    (nhdsWithin_mono _ (fun _ ha => ne_of_lt ha))

end QuantumChannelContinuity
