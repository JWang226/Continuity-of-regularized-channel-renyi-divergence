import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scalar reductions of the binary testing inequalities

These lemmas prove the algebra, base-two exponentiation, and passage to a
supremum in the manuscript's testing lemma. The quantum binary data-processing
bounds are explicit hypotheses; this file does not identify abstract scalars
with quantum relative entropies.
-/

namespace ChannelContinuity

/-- The relative-entropy binary testing inequality bounds the testing payoff.
The real variable `n` allows direct specialization to positive natural block
sizes without making the elementary calculation depend on coercions. -/
theorem weak_testing_bound {n r d p objective : ℝ}
    (hn : 0 < n) (hr : 0 < r)
    (hdata : (n * r) * p - 1 ≤ n * d) (hobjective : objective ≤ p) :
    objective ≤ d / r + 1 / (n * r) := by
  have hp : p ≤ (n * d + 1) / (n * r) :=
    (le_div_iff₀ (mul_pos hn hr)).2 (by nlinarith)
  calc
    objective ≤ p := hobjective
    _ ≤ (n * d + 1) / (n * r) := hp
    _ = d / r + 1 / (n * r) := by
      field_simp [ne_of_gt hn, ne_of_gt hr]

/-- Base-two exponentiation turns the Rényi binary data-processing inequality
into the high-rate exponential estimate. Positivity of `n` or of the rate gap
is not needed for this algebraic implication. -/
theorem high_testing_bound {n alpha a ell p objective : ℝ}
    (halpha : 1 < alpha) (hp : 0 < p)
    (hdata : n * ell + (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a)
    (hobjective : objective ≤ p) :
    objective ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  have ha : 0 < alpha - 1 := sub_pos.mpr halpha
  have hlogdiv : Real.logb 2 p / (alpha - 1) ≤ n * a - n * ell := by
    rw [div_eq_mul_inv]
    simpa only [one_div, mul_comm] using
      (show (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a - n * ell by linarith)
  have hlog := (div_le_iff₀ ha).1 hlogdiv
  have hpbound : p ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
    apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).1
    nlinarith
  exact hobjective.trans hpbound

/-- Include zero acceptance probability, where the payoff is already
nonpositive and no logarithm bound is required. -/
theorem high_testing_bound_of_nonneg {n alpha a ell p objective : ℝ}
    (halpha : 1 < alpha) (hp : 0 ≤ p)
    (hdata : 0 < p → n * ell + (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a)
    (hobjective : objective ≤ p) :
    objective ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  rcases eq_or_lt_of_le hp with hpzero | hppos
  · have hzero : objective ≤ 0 := by simpa [← hpzero] using hobjective
    exact hzero.trans (Real.rpow_nonneg (by norm_num) _)
  · exact high_testing_bound halpha hppos (hdata hppos) hobjective

/-- A uniform weak testing bound passes to the supremum over inputs and tests. -/
theorem weak_testing_sup_bound {ι : Type*} [Nonempty ι]
    {objective p : ι → ℝ} {n r d : ℝ}
    (hn : 0 < n) (hr : 0 < r)
    (hdata : ∀ i, (n * r) * p i - 1 ≤ n * d)
    (hobjective : ∀ i, objective i ≤ p i) :
    sSup (Set.range objective) ≤ d / r + 1 / (n * r) := by
  apply csSup_le (Set.range_nonempty objective)
  rintro _ ⟨i, rfl⟩
  exact weak_testing_bound hn hr (hdata i) (hobjective i)

/-- A uniform high-rate bound passes to the supremum, allowing tests with zero
acceptance probability and avoiding existence of an optimizing test. -/
theorem high_testing_sup_bound {ι : Type*} [Nonempty ι]
    {objective p : ι → ℝ} {n alpha a ell : ℝ}
    (halpha : 1 < alpha) (hp : ∀ i, 0 ≤ p i)
    (hdata : ∀ i, 0 < p i →
      n * ell + (1 / (alpha - 1)) * Real.logb 2 (p i) ≤ n * a)
    (hobjective : ∀ i, objective i ≤ p i) :
    sSup (Set.range objective) ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  apply csSup_le (Set.range_nonempty objective)
  rintro _ ⟨i, rfl⟩
  exact high_testing_bound_of_nonneg halpha (hp i) (hdata i) (hobjective i)

/-- In the hockey-stick argument the binary inequality is only needed for
strictly positive payoff. Nonpositive payoffs already satisfy the bound. -/
theorem high_testing_bound_of_positive_payoff {n alpha a ell p objective : ℝ}
    (halpha : 1 < alpha) (hobjective : objective ≤ p)
    (hdata : 0 < objective →
      n * ell + (1 / (alpha - 1)) * Real.logb 2 p ≤ n * a) :
    objective ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  by_cases hpos : 0 < objective
  · exact high_testing_bound halpha (hpos.trans_le hobjective) (hdata hpos) hobjective
  · exact (le_of_not_gt hpos).trans (Real.rpow_nonneg (by norm_num) _)

/-- The preceding form passes to the channel supremum, so the data-processing
estimate is required only for testers with strictly positive payoff. -/
theorem high_testing_sup_bound_of_positive_payoff {ι : Type*} [Nonempty ι]
    {objective p : ι → ℝ} {n alpha a ell : ℝ}
    (halpha : 1 < alpha) (hobjective : ∀ i, objective i ≤ p i)
    (hdata : ∀ i, 0 < objective i →
      n * ell + (1 / (alpha - 1)) * Real.logb 2 (p i) ≤ n * a) :
    sSup (Set.range objective) ≤ (2 : ℝ) ^ (-n * (alpha - 1) * (ell - a)) := by
  apply csSup_le (Set.range_nonempty objective)
  rintro _ ⟨i, rfl⟩
  exact high_testing_bound_of_positive_payoff halpha (hobjective i) (hdata i)

/-- The weak estimate likewise only needs binary data processing on testers
whose hockey-stick payoff is positive. -/
theorem weak_testing_bound_of_positive_payoff {n r d p objective : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hd : 0 ≤ d) (hobjective : objective ≤ p)
    (hdata : 0 < objective → (n * r) * p - 1 ≤ n * d) :
    objective ≤ d / r + 1 / (n * r) := by
  by_cases hpos : 0 < objective
  · exact weak_testing_bound hn hr (hdata hpos) hobjective
  · apply (le_of_not_gt hpos).trans
    exact add_nonneg (div_nonneg hd hr.le)
      (div_nonneg zero_le_one (mul_pos hn hr).le)

/-- Uniform weak testing estimates for positive payoffs bound the supremum. -/
theorem weak_testing_sup_bound_of_positive_payoff {ι : Type*} [Nonempty ι]
    {objective p : ι → ℝ} {n r d : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hd : 0 ≤ d)
    (hobjective : ∀ i, objective i ≤ p i)
    (hdata : ∀ i, 0 < objective i → (n * r) * p i - 1 ≤ n * d) :
    sSup (Set.range objective) ≤ d / r + 1 / (n * r) := by
  apply csSup_le (Set.range_nonempty objective)
  rintro _ ⟨i, rfl⟩
  exact weak_testing_bound_of_positive_payoff hn hr hd (hobjective i) (hdata i)

end ChannelContinuity
