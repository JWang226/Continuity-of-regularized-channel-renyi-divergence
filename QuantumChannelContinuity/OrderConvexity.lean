import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

/-! # Scalar conversion from interpolation convexity to Rényi order -/

open Set
namespace QuantumChannelContinuity

theorem reciprocal_order_mem {α : ℝ} (hα : 1 / 2 < α) :
    1 / (2 * α) ∈ Ioo (0 : ℝ) 1 := by
  have hα0 : 0 < 2 * α := by linarith
  exact ⟨one_div_pos.mpr hα0, (div_lt_one hα0).mpr (by linarith)⟩

theorem reciprocal_order_ne_half {α : ℝ} (hα : 1 / 2 < α) (hα1 : α ≠ 1) :
    1 / (2 * α) ≠ (1 / 2 : ℝ) := by
  have hα0 : 0 < 2 * α := by linarith
  intro h
  have hh := (div_eq_iff hα0.ne').mp h
  apply hα1
  linarith

/-- Increasing Rényi order reverses the reciprocal interpolation parameter.
Convex secant slopes therefore give the required monotonicity on both sides
of one (and across it), with no endpoint differentiability assumption. -/
theorem renyi_order_of_convex_log_norm {g : ℝ → ℝ}
    (hg : ConvexOn ℝ (Ioo 0 1) g) (hcenter : g (1 / 2) = 0)
    {α β : ℝ} (hα : 1 / 2 < α) (hα1 : α ≠ 1) (hβ1 : β ≠ 1)
    (hαβ : α ≤ β) :
    -g (1 / (2 * α)) / (1 / (2 * α) - 1 / 2) ≤
      -g (1 / (2 * β)) / (1 / (2 * β) - 1 / 2) := by
  have hβ : 1 / 2 < β := hα.trans_le hαβ
  have hparam : 1 / (2 * β) ≤ 1 / (2 * α) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hs := hg.secant_mono (a := (1 / 2 : ℝ)) (by norm_num)
    (reciprocal_order_mem hβ) (reciprocal_order_mem hα)
    (reciprocal_order_ne_half hβ hβ1) (reciprocal_order_ne_half hα hα1) hparam
  simpa only [hcenter, sub_zero, neg_div] using neg_le_neg hs

end QuantumChannelContinuity
