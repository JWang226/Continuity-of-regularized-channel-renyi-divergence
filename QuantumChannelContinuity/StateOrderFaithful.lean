import QuantumChannelContinuity.StateOrderInterpolation
import QuantumChannelContinuity.StateOrderDuality
import QuantumChannelContinuity.StateOrderBoundaryNorms
import QuantumChannelContinuity.ComplexTraceHolder

/-! # Weighted Schatten interpolation and faithful Rényi order comparisons -/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Hölder gives the exact boundary norm for the holomorphic duality
family; all imaginary powers and the polar unitary are handled explicitly. -/
theorem weighted_trace_boundary {X σ : L H} (hX : IsStrictlyPositive X)
    (hσ : IsStrictlyPositive σ) (hTr : (Tr X).re = 1) (U : unitary (L H)) (R : L H)
    {p : ℝ} (hp : 1 < p) {z w : ℂ} (hz : z.re = 1 - 1 / p)
    (hw : w.re = 1 / p - 1 / 2) :
    ‖Tr (operatorCpow X z * star (U : L H) * R * operatorCpow σ w)‖ ≤
      schattenNorm (R * CFC.rpow σ (1 / p - 1 / 2)) p := by
  let q := p / (p - 1)
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hzq : z.re = 1 / q := by
    rw [hz]
    simpa only [one_div] using hpq.one_sub_inv
  have h := complex_trace_holder hpq.symm
    (operatorCpow X z * star (U : L H)) (R * operatorCpow σ w)
  have hnorm := normalized_dual_power_trace hX hTr U (q := q) (z := z) hpq.symm.lt hzq
  rw [hnorm, one_mul,
    mul_operatorCpow_density_eq_re hσ R w, hw] at h
  have hswap := trace_rpow_star_mul_swap (R * CFC.rpow σ (1 / p - 1 / 2)) (p / 2)
  simpa only [schattenNorm, schattenWeight, hswap, mul_assoc] using h

/-- Weighted interpolation between any two Schatten exponents greater
than one. This is proved from the actual analytic trace family and dual
attainment; no operator interpolation inequality is an input. -/
theorem faithful_weighted_schatten_interpolation {σ R : L H}
    (hσ : IsStrictlyPositive σ) (hR : IsUnit R)
    {t₀ t₁ θ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (ht₁ : t₁ ∈ Ioo 0 1)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    let t := (1 - θ) * t₀ + θ * t₁
    schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) ≤
      schattenNorm (R * CFC.rpow σ (t₀ - 1 / 2)) (1 / t₀) ^ (1 - θ) *
      schattenNorm (R * CFC.rpow σ (t₁ - 1 / 2)) (1 / t₁) ^ θ := by
  let t := (1 - θ) * t₀ + θ * t₁
  change schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) ≤ _
  have ht : t ∈ Ioo 0 1 := by
    constructor
    · have h₀ := mul_nonneg (sub_nonneg.mpr hθ₁) ht₀.1.le
      have h₁ := mul_nonneg hθ₀ ht₁.1.le
      by_cases hz : θ = 0
      · simp [t, hz, ht₀.1]
      · have hpos := mul_pos (lt_of_le_of_ne hθ₀ (Ne.symm hz)) ht₁.1
        dsimp [t]; linarith
    · have h₀ := mul_nonneg (sub_nonneg.mpr hθ₁) (sub_pos.mpr ht₀.2).le
      have h₁ := mul_nonneg hθ₀ (sub_pos.mpr ht₁.2).le
      by_cases hz : θ = 0
      · simp [t, hz, ht₀.2]
      · have hpos := mul_pos (lt_of_le_of_ne hθ₀ (Ne.symm hz)) (sub_pos.mpr ht₁.2)
        dsimp [t]; nlinarith
  have hp : 1 < 1 / t := (one_lt_div ht.1).2 ht.2
  have hC : IsUnit (R * CFC.rpow σ (t - 1 / 2)) := hR.mul hσ.rpow.isUnit
  obtain ⟨X, U, hX, hTr, hdual⟩ := exists_faithful_schatten_dual hC hp
  have hF := operatorTraceFamily_three_lines X σ (star (U : L H)) R
    (1 - t₀) (1 - t₁) (t₀ - 1 / 2) (t₁ - 1 / 2) hθ₀ hθ₁
    (by
      intro z hz
      apply weighted_trace_boundary hX hσ hTr U R ((one_lt_div ht₀.1).2 ht₀.2)
      · simp [stripExponent_re, hz]
      · simp [stripExponent_re, hz])
    (by
      intro z hz
      apply weighted_trace_boundary hX hσ hTr U R ((one_lt_div ht₁.1).2 ht₁.2)
      · simp [stripExponent_re, hz]
      · simp [stripExponent_re, hz])
  have ha : stripExponent (1 - t₀) (1 - t₁) (θ : ℂ) = ((1 - t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [stripExponent, t] <;> ring
  have hb : stripExponent (t₀ - 1 / 2) (t₁ - 1 / 2) (θ : ℂ) = ((t - 1 / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [stripExponent, t] <;> ring
  rw [operatorTraceFamily, ha, hb, operatorCpow_ofReal hX, operatorCpow_ofReal hσ] at hF
  have hdual' : ‖Tr (CFC.rpow X (1 - t) * star (U : L H) * R * CFC.rpow σ (t - 1 / 2))‖ =
      schattenNorm (R * CFC.rpow σ (t - 1 / 2)) (1 / t) := by
    simpa only [one_div_one_div, mul_assoc] using hdual
  rw [hdual'] at hF
  simpa only [one_div_one_div] using hF

end QuantumChannelContinuity
