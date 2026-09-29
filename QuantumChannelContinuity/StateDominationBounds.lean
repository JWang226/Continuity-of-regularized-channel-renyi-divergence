import QuantumChannelContinuity.TracePowerBounds

/-!
# Uniform state-divergence bounds from operator domination

These results discharge finiteness and cap bounds. The proof of the Umegaki
bound passes through faithful perturbations and their proved boundary limit,
so it covers support-included singular, noncommuting states.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]

/-- Domination implies support inclusion, with no invertibility assumption. -/
theorem suppLE_of_nonneg_le_smul {ρ σ : L H} (hρ : 0 ≤ ρ) {c : ℝ}
    (hdom : ρ ≤ c • σ) : suppLE ρ σ := by
  intro x hx
  apply nonneg_eq_zero_of_le_of_apply_eq_zero hρ hdom
  change c • σ x = 0
  rw [show σ x = 0 from hx, smul_zero]

/-- Above one, the coarse all-order trace bound gives an explicit finite
upper bound for the normalized state divergence. -/
theorem stateRenyi_le_coarse_log_of_le {p c : ℝ} (hp : 1 < p) (hc : 0 < c)
    (ρ σ : DensityState H) (hdom : ρ.op ≤ c • σ.op) :
    stateRenyi p ρ σ ≤ ((p / (p - 1)) * Real.logb 2 c : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hs := suppLE_of_nonneg_le_smul ρ.nonneg hdom
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ.op σ.op ρ.nonneg σ.nonneg hs ρ.op_ne_zero
  have hbound := sandwichedQuasi_le_power_trace hp ρ.op σ.op
    ((LinearMap.nonneg_iff_isPositive _).mp ρ.nonneg)
    ((LinearMap.nonneg_iff_isPositive _).mp σ.nonneg) hc.le hdom
  rw [σ.trace_one, Complex.one_re, mul_one] at hbound
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hQ hbound
  rw [Real.logb_rpow_eq_mul_logb_of_pos hc] at hlog
  rw [stateRenyi_eq_formula hp ρ σ hs, EReal.coe_le_coe_iff]
  have h := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (sub_pos.mpr hp).le)
  convert h using 1 <;> ring

/-- The sharp near-one bound for unnormalized positive operators. -/
theorem sandwichedRenyiDiv_le_log_of_le {p c : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hc : 0 < c) {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hdom : ρ ≤ c • σ) : sandwichedRenyiDiv p ρ σ ≤ Real.log c := by
  have hp0 : 0 < p := by linarith
  have ht : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  have hs := suppLE_of_nonneg_le_smul hρ hdom
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ σ hρ hσ hs hρ0
  have hbound := sandwichedQuasi_le_of_le hp hp2 ρ σ
    ((LinearMap.nonneg_iff_isPositive _).mp hρ)
    ((LinearMap.nonneg_iff_isPositive _).mp hσ) hc.le hdom
  have hquot : (sandwichedQuasi p ρ σ).re / (Tr ρ).re ≤ c ^ (p - 1) :=
    (div_le_iff₀ ht).mpr hbound
  have hlog := Real.log_le_log (div_pos hQ ht) hquot
  rw [Real.log_rpow hc] at hlog
  have h := mul_le_mul_of_nonneg_left hlog (one_div_nonneg.mpr (sub_pos.mpr hp).le)
  change (1 / (p - 1)) * Real.log ((sandwichedQuasi p ρ σ).re / (Tr ρ).re) ≤ _
  convert h using 1
  field_simp [ne_of_gt (sub_pos.mpr hp)]

/-- The Umegaki domination bound for faithful, not necessarily normalized operators. -/
theorem umegakiNorm_le_log_of_le_pd {c : ℝ} (hc : 0 < c)
    {ρ σ : L H} (hρ : ρ ∈ pdSetLM) (hσ : σ ∈ pdSetLM)
    (hdom : ρ ≤ c • σ) : umegakiNorm ρ σ ≤ Real.log c := by
  apply le_of_tendsto (sandwichedRenyiDiv_tendsto_umegaki hρ hσ)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds]
    with p hp hp2
  exact sandwichedRenyiDiv_le_log_of_le hp hp2.le hc
    (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)
    (by intro hz; have h := trace_re_pos_of_pdSetLM hρ; simp [hz] at h) hdom

/-- The same Umegaki bound for arbitrary support-included nonnegative
operators. Faithful perturbations preserve the domination constant `c≥1`. -/
theorem umegakiNorm_le_log_of_le {c : ℝ} (hc : 1 ≤ c)
    {ρ σ : L H} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hdom : ρ ≤ c • σ) : umegakiNorm ρ σ ≤ Real.log c := by
  have hs := suppLE_of_nonneg_le_smul hρ hdom
  apply le_of_tendsto (tendsto_umegakiNorm_perturb hρ hσ hρ0 hs)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  apply umegakiNorm_le_log_of_le_pd (zero_lt_one.trans_le hc)
    (pdSetLM_add_nonneg hρ (pos_smul_one_pdSetLM hεpos))
    (pdSetLM_add_nonneg hσ (pos_smul_one_pdSetLM hεpos))
  have hεone : (ε : ℂ) • (1 : L H) ≤ c • ((ε : ℂ) • (1 : L H)) := by
    have hnn : 0 ≤ (ε : ℂ) • (1 : L H) :=
      smul_nonneg (by exact_mod_cast hεpos.le) zero_le_one
    simpa only [one_smul] using smul_le_smul_of_nonneg_right hc hnn
  simpa only [smul_add] using add_le_add hdom hεone

/-- Finite max-relative domination bounds the actual support-aware state
relative entropy in bits, including singular states. -/
theorem stateRelative_le_log_of_le {c : ℝ} (hc : 1 ≤ c)
    (ρ σ : DensityState H) (hdom : ρ.op ≤ c • σ.op) :
    stateRelative ρ σ ≤ (Real.logb 2 c : ℝ) := by
  have hs := suppLE_of_nonneg_le_smul ρ.nonneg hdom
  have h := umegakiNorm_le_log_of_le hc ρ.nonneg σ.nonneg ρ.op_ne_zero hdom
  have hb := toBits_mono (EReal.coe_le_coe_iff.mpr h)
  simpa only [stateRelative, umegakiRelEntropyNN, hs, ↓reduceIte, toBits_coe,
    Real.logb] using hb

end QuantumChannelContinuity
