import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# From a strict testing limsup to an eventual square-root bound

The manuscript's hockey-stick sequence lies in `[0,1]`, hence is bounded above.
This boundedness is mathematically necessary when using the real-valued
`Filter.limsup`: an unbounded-above sequence has no eventual real upper bound,
so the defining infimum is empty and its value is the real default `0`.
Consequently, nonnegativity and `limsup E < 1` alone do not suffice.

Only eventual upper boundedness is needed here. Nonnegativity of `E` is not
required for this auxiliary lemma because `Real.sqrt` is monotone on all reals.
-/

open Filter

namespace ChannelContinuity

/-- A real sequence with a genuine bounded limsup below one has an eventual
square-root bound strictly below one. This is the testing premise of the
manuscript's threshold criterion. -/
theorem eventual_sqrt_bound_of_limsup_lt_one {E : ℕ → ℝ}
    (hbounded : atTop.IsBoundedUnder (· ≤ ·) E)
    (hlimsup : Filter.limsup E atTop < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ ∀ᶠ n in atTop, Real.sqrt (E n) ≤ B := by
  obtain ⟨c, hc, hc1⟩ := exists_between hlimsup
  refine ⟨Real.sqrt c, Real.sqrt_nonneg _, ?_, ?_⟩
  · exact lt_of_not_ge fun h => (not_le_of_gt hc1) (Real.one_le_sqrt.mp h)
  · filter_upwards [eventually_lt_of_limsup_lt hc hbounded] with n hn
    exact Real.sqrt_le_sqrt hn.le

/-- The directly applicable form for a hockey-stick sequence, whose values
are at most one. -/
theorem eventual_sqrt_bound_of_limsup_lt_one_of_le_one {E : ℕ → ℝ}
    (hupper : ∀ n, E n ≤ 1)
    (hlimsup : Filter.limsup E atTop < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ ∀ᶠ n in atTop, Real.sqrt (E n) ≤ B :=
  eventual_sqrt_bound_of_limsup_lt_one
    (Filter.isBoundedUnder_of ⟨1, hupper⟩) hlimsup

end ChannelContinuity
