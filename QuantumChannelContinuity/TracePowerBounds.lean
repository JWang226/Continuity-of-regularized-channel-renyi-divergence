import QuantumChannelContinuity.DivergenceSchatten

/-!
# Trace-power bounds at every order above one

A scalar trace moment is monotone even when the corresponding operator power
is not operator-monotone. Trace Hölder proves this directly, and gives the
uniform bounds required to establish finiteness of channel regularizations.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct ENNReal
namespace QuantumChannelContinuity

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [Qudit H]

/-- Trace powers preserve positive-operator order for every real `p>1`.
The proof uses trace Hölder, with no operator-monotonicity assumption. -/
theorem trace_rpow_re_mono {p : ℝ} (hp : 1 < p)
    {X Y : L H} (hX : X.IsPositive) (hY : Y.IsPositive) (hXY : X ≤ Y) :
    (Tr (CFC.rpow X p)).re ≤ (Tr (CFC.rpow Y p)).re := by
  let q : ℝ := p / (p - 1)
  have hpm : 0 < p - 1 := sub_pos.mpr hp
  have hpq : p.HolderConjugate q :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  let R := (Tr (CFC.rpow X p)).re
  let S := (Tr (CFC.rpow Y p)).re
  let W := CFC.rpow X (p - 1)
  have hR : 0 ≤ R := trace_rpow_re_nonneg X p
  have hS : 0 ≤ S := trace_rpow_re_nonneg Y p
  have hW : W.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hWq : CFC.rpow W q = CFC.rpow X p := by
    dsimp only [W]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg X (p - 1) q (by linarith)
      hpq.symm.nonneg ((LinearMap.nonneg_iff_isPositive _).mpr hX)]
    congr 1
    dsimp [q]
    field_simp
  have hRX : (Tr (X * W)).re = R := by
    rw [LinearMap.trace_mul_comm ℂ X W]
    exact congrArg Complex.re (congrArg Tr (rpow_sub_one_mul_self X hX hp))
  have hbound : R ≤ S ^ (1 / p) * R ^ (1 / q) := by
    calc
      R = (Tr (X * W)).re := hRX.symm
      _ ≤ (Tr (Y * W)).re := trace_mul_re_mono hXY W hW
      _ ≤ S ^ (1 / p) * R ^ (1 / q) := by
        have ht := trace_holder hpq Y W hY hW
        simpa only [hWq] using ht
  change R ≤ S
  rcases eq_or_lt_of_le hR with hz | hRpos
  · rw [← hz]
    exact hS
  · have hfact : R = R ^ (1 / p) * R ^ (1 / q) := by
      rw [← Real.rpow_add hRpos, hpq.one_div_add_one_div, div_one, Real.rpow_one]
    nth_rw 1 [hfact] at hbound
    have hroot : R ^ (1 / p) ≤ S ^ (1 / p) :=
      le_of_mul_le_mul_right hbound (Real.rpow_pos_of_pos hRpos _)
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hR _) hroot hpq.nonneg
    simpa only [← Real.rpow_mul hR, ← Real.rpow_mul hS,
      one_div_mul_cancel hpq.ne_zero, Real.rpow_one] using h

/-- A coarse bound at every order above one. Its constant is sufficient to
prove finiteness after dividing channel-block divergences by block length. -/
theorem sandwichedQuasi_le_power_trace {p : ℝ} (hp : 1 < p)
    (ρ σ : L H) (hρ : ρ.IsPositive) (hσ : σ.IsPositive)
    {c : ℝ} (hc : 0 ≤ c) (hdom : ρ ≤ c • σ) :
    (sandwichedQuasi p ρ σ).re ≤ c ^ p * (Tr σ).re := by
  let a : ℝ := (1 - p) / (2 * p)
  let S : L H := CFC.rpow σ a
  let X : L H := S * ρ * S
  let Y : L H := CFC.rpow σ (1 / p)
  have hp0 : 0 < p := by linarith
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hX : X.IsPositive := by
    have h := hρ.conj_adjoint S
    simpa only [hS.adjoint_eq] using h
  have hY : Y.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg
  have hexp : a + 1 + a = 1 / p := by dsimp [a]; field_simp; ring
  have ha1 : a + 1 ≠ 0 := by
    have heq : a + 1 = (p + 1) / (2 * p) := by dsimp [a]; field_simp; ring
    rw [heq]
    positivity
  have hSσS : S * σ * S = Y := by
    have hσpow : σ = CFC.rpow σ 1 :=
      (CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).mpr hσ)).symm
    calc
      S * σ * S = CFC.rpow σ a * CFC.rpow σ 1 * CFC.rpow σ a := by rw [← hσpow]
      _ = CFC.rpow σ (a + 1) * CFC.rpow σ a := by
        rw [operator_rpow_mul σ hσ a 1 ha1]
      _ = CFC.rpow σ (a + 1 + a) :=
        operator_rpow_mul σ hσ _ _ (by rw [hexp]; positivity)
      _ = Y := by rw [hexp]
  have hXY : X ≤ c • Y := by
    have h := hS.isSelfAdjoint.conjugate_le_conjugate hdom
    simpa only [mul_smul_comm, smul_mul_assoc, hSσS] using h
  have hcY : (c • Y).IsPositive :=
    (LinearMap.nonneg_iff_isPositive _).mp (smul_nonneg hc CFC.rpow_nonneg)
  have hpow : CFC.rpow (c • Y) p = c ^ p • σ := by
    rw [operator_rpow_smul Y hY hc]
    congr 1
    dsimp only [Y]
    simp only [CFC.rpow_eq_pow]
    rw [CFC.rpow_rpow_of_exponent_nonneg σ (1 / p) p (by positivity) hp0.le
      ((LinearMap.nonneg_iff_isPositive _).mpr hσ), one_div_mul_cancel hp0.ne',
      CFC.rpow_one σ ((LinearMap.nonneg_iff_isPositive _).mpr hσ)]
  have ht := trace_rpow_re_mono hp hX hcY hXY
  rw [hpow] at ht
  simpa only [sandwichedQuasi, a, S, X, LinearMap.map_smul_of_tower, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using ht

end QuantumChannelContinuity
