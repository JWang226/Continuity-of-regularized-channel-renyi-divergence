import QuantumChannelContinuity.StateOrderFaithful
import QuantumChannelContinuity.StateOrderBoundary
import QuantumChannelContinuity.OrderConvexity

/-! # From weighted Schatten interpolation to Rényi order monotonicity

The logarithm of the weighted Schatten norm is convex in reciprocal order.
Its value at reciprocal order one half is zero, so its secant slopes give
monotonicity of the actual sandwiched Rényi divergence on faithful states.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable def weightedSchattenLog (ρ σ : L H) (t : ℝ) : ℝ :=
  Real.log (schattenNorm (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (t - 1 / 2)) (1 / t))

theorem sqrt_weighted_density (ρ σ : L H) (hρ : IsStrictlyPositive ρ) (t : ℝ) :
    star (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ t) *
      (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ t) = CFC.rpow σ t * ρ * CFC.rpow σ t := by
  have hstar (X : L H) (a : ℝ) : star (CFC.rpow X a) = CFC.rpow X a :=
    CFC.rpow_nonneg.isSelfAdjoint.star_eq
  have hsq : CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow ρ (1 / 2 : ℝ) = ρ := by
    calc
      _ = CFC.rpow ρ ((1 / 2 : ℝ) + 1 / 2) := (CFC.rpow_add hρ.isUnit).symm
      _ = ρ := by norm_num only; exact CFC.rpow_one _ hρ.nonneg
  rw [star_mul, hstar, hstar, mul_assoc, ← mul_assoc (CFC.rpow ρ (1 / 2 : ℝ)), hsq, mul_assoc]

theorem sqrt_weighted_schattenWeight (ρ σ : L H) (hρ : IsStrictlyPositive ρ)
    {α : ℝ} (hα : α ≠ 0) :
    schattenWeight (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (1 / (2 * α) - 1 / 2))
      (2 * α) = (sandwichedQuasi α ρ σ).re := by
  unfold schattenWeight sandwichedQuasi
  rw [sqrt_weighted_density ρ σ hρ]
  have hexp : 1 / (2 * α) - 1 / 2 = (1 - α) / (2 * α) := by field_simp
  rw [hexp]
  congr 3
  ring

theorem weightedSchattenLog_eq_log_quasi (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ)
    {α : ℝ} (hα : α ≠ 0) :
    weightedSchattenLog ρ σ (1 / (2 * α)) =
      (1 / (2 * α)) * Real.log (sandwichedQuasi α ρ σ).re := by
  have hC : IsUnit (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (1 / (2 * α) - 1 / 2)) :=
    hρ.rpow.isUnit.mul hσ.rpow.isUnit
  unfold weightedSchattenLog schattenNorm
  rw [one_div_one_div, Real.log_rpow (schattenWeight_pos hC _),
    sqrt_weighted_schattenWeight ρ σ hρ hα]

theorem weightedSchattenLog_half (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) (hTr : (Tr ρ).re = 1) :
    weightedSchattenLog ρ σ (1 / 2) = 0 := by
  have hweight : schattenWeight
      (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ ((1 / 2 : ℝ) - 1 / 2)) (1 / (1 / 2 : ℝ)) = 1 := by
    unfold schattenWeight
    rw [sqrt_weighted_density ρ σ hρ]
    norm_num only
    simp only [CFC.rpow_eq_pow, CFC.rpow_zero σ hσ.nonneg, one_mul, mul_one,
      CFC.rpow_one ρ hρ.nonneg, hTr]
  unfold weightedSchattenLog schattenNorm
  rw [hweight, Real.one_rpow, Real.log_one]

/-- Complex interpolation gives genuine log-convexity in reciprocal order. -/
theorem weightedSchattenLog_convex (ρ σ : L H)
    (hρ : IsStrictlyPositive ρ) (hσ : IsStrictlyPositive σ) :
    ConvexOn ℝ (Ioo 0 1) (weightedSchattenLog ρ σ) := by
  have hunit (t : ℝ) : IsUnit (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (t - 1 / 2)) :=
    hρ.rpow.isUnit.mul hσ.rpow.isUnit
  have hpos (t : ℝ) :
      0 < schattenNorm (CFC.rpow ρ (1 / 2 : ℝ) * CFC.rpow σ (t - 1 / 2)) (1 / t) :=
    schattenNorm_pos (hunit t) _
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hab' : 1 - b = a := by linarith
  have h := faithful_weighted_schatten_interpolation hσ
    (show IsUnit (CFC.rpow ρ (1 / 2 : ℝ)) from hρ.rpow.isUnit) hx hy hb hb1
  dsimp only at h
  have hl := Real.log_le_log (hpos ((1 - b) * x + b * y)) h
  rw [Real.log_mul (Real.rpow_pos_of_pos (hpos x) (1 - b)).ne'
    (Real.rpow_pos_of_pos (hpos y) b).ne', Real.log_rpow (hpos x), Real.log_rpow (hpos y)] at hl
  simpa only [weightedSchattenLog, smul_eq_mul, hab'] using hl

/-- The actual base-two divergence is the negative secant slope of the
logarithmic weighted norm through reciprocal order one half. -/
theorem stateRenyi_eq_weighted_secant {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi α ρ σ =
      (((-weightedSchattenLog ρ.op σ.op (1 / (2 * α)) /
        (1 / (2 * α) - 1 / 2)) / Real.log 2 : ℝ) : EReal) := by
  rw [OrderBoundary.stateRenyi_eq_coe_pd hα ρ σ hρ hσ,
    weightedSchattenLog_eq_log_quasi ρ.op σ.op
      (isStrictlyPositive_of_pdSetLM hρ) (isStrictlyPositive_of_pdSetLM hσ) hα.ne']
  simp only [sandwichedRenyiDiv, ρ.trace_one, Complex.one_re, div_one]
  congr 1
  have hαsub : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
  have h1sub : 1 - α ≠ 0 := sub_ne_zero.mpr hα1.symm
  field_simp [hα.ne', hαsub, h1sub]
  ring

/-- Faithful state Rényi divergence is monotone in its order, both above
and below one and also across one. All interpolation inputs are proved. -/
theorem stateRenyi_le_of_faithful {α β : ℝ} (hα : 1 / 2 < α)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≤ β)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  have hρp := isStrictlyPositive_of_pdSetLM hρ
  have hσp := isStrictlyPositive_of_pdSetLM hσ
  have h := renyi_order_of_convex_log_norm
    (weightedSchattenLog_convex ρ.op σ.op hρp hσp)
    (weightedSchattenLog_half ρ.op σ.op hρp hσp (by rw [ρ.trace_one]; rfl))
    hα hα1 hβ1 hαβ
  rw [stateRenyi_eq_weighted_secant (by linarith) hα1 ρ σ hρ hσ,
    stateRenyi_eq_weighted_secant (by linarith) hβ1 ρ σ hρ hσ, EReal.coe_le_coe_iff]
  exact div_le_div_of_nonneg_right h log_two_pos.le

end QuantumChannelContinuity
