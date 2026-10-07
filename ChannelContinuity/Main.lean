/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import ChannelContinuity.LeftContinuity
import ChannelContinuity.Threshold
import ChannelContinuity.ThreePiece
import ChannelContinuity.OperatorAlgebra
import ChannelContinuity.Parameters
import ChannelContinuity.Testing
import ChannelContinuity.Limsup
import Mathlib.Tactic.Positivity

/-!
# Conditional formalization of Theorem 1

The successive limit passages, testing-threshold argument, and left/right
assembly are proved. `FiniteAnalyticInputs` explicitly records the
quantum-information facts still to be connected to concrete channels.
In particular, its `raw_schatten` field is the exponentiated consequence of the
manuscript's filtering and Schatten arguments, not an operator theorem proved
in this project. Its subsequent scalar normalization is proved here.

These are scalar data and explicit proof obligations. The concrete extension
in `QuantumChannelContinuity/ConcreteMain.lean` now constructs all testing
fields from actual channel tensor powers. Full construction of the remaining
order and regularized-decomposition fields is still open. See README.md.
-/

open Filter Set
open scoped Topology ENNReal

namespace ChannelContinuity

/-- The finite-case scalar quantities and the unformalized quantum bridge.

Intended interpretations:
* `d` = regularized channel relative entropy;
* `renyi a` = regularized sandwiched channel Rényi divergence;
* `cap` = finite channel max-relative entropy;
* `testing n r` = hockey-stick divergence at threshold `2^(n*r)`.

The input hypotheses are deliberately visible rather than global axioms.
-/
structure FiniteAnalyticInputs where
  d : ℝ
  renyi : ℝ → ℝ
  cap : ℝ
  testing : ℕ → ℝ → ℝ
  d_nonneg : 0 ≤ d
  order_mono : MonotoneOn renyi (Ioi 1)
  relative_le_renyi : ∀ a, 1 < a → d ≤ renyi a
  testing_nonneg : ∀ n r, 0 ≤ testing n r
  weak_testing : ∀ r, 0 < r → ∀ n : ℕ, 0 < n →
    testing n r ≤ d / r + 1 / ((n : ℝ) * r)
  renyi_testing : ∀ a, 1 < a → ∀ ell, renyi a < ell → ∀ n : ℕ, 0 < n →
    testing n ell ≤ (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - renyi a))
  raw_schatten : ∀ r, 0 ≤ r → r < sInf (renyi '' Ioi 1) →
    ∀ t : ℝ, 1 ≤ t → ∀ n : ℕ, t < (n : ℝ) → 2 * t ≤ (n : ℝ) →
      (2 : ℝ) ^ (t * sInf (renyi '' Ioi 1) / 2) ≤
      rawSchattenRhs n t r (sInf (renyi '' Ioi 1)) cap
        (Real.sqrt (testing n r))
        (Real.sqrt (testing n (sInf (renyi '' Ioi 1) + 1 / (t * t))))

/-- Derive the normalized estimate, including the eventually valid condition
`n > t`, from the raw exponentiated Schatten hypothesis. -/
theorem FiniteAnalyticInputs.three_piece (h : FiniteAnalyticInputs)
    (r : ℝ) (hr : 0 ≤ r) (hgap : r < sInf (h.renyi '' Ioi 1))
    (t : ℝ) (ht : 1 ≤ t) : ∀ᶠ n : ℕ in atTop,
      1 ≤ threePieceRhs n t r (sInf (h.renyi '' Ioi 1)) h.cap
        (Real.sqrt (h.testing n r))
        (Real.sqrt (h.testing n (sInf (h.renyi '' Ioi 1) + 1 / (t * t)))) := by
  have hn : ∀ᶠ n : ℕ in atTop, 2 * t < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (2 * t))
  filter_upwards [hn] with n h2tn
  have htn : t < (n : ℝ) := by linarith
  exact three_piece_bound_of_raw_schatten ht htn
    (h.raw_schatten r hr hgap t ht n htn h2tn.le)

/-- Amplification from a fixed eventual error strictly below one, with both
successive limits checked. -/
theorem FiniteAnalyticInputs.threshold_le_of_eventual_sqrt_bound
    (h : FiniteAnalyticInputs) {r B : ℝ} (hr : 0 ≤ r) (hBlt : B < 1)
    (hBevent : ∀ᶠ n in atTop, Real.sqrt (h.testing n r) ≤ B) :
    sInf (h.renyi '' Ioi 1) ≤ r := by
  by_cases hdone : sInf (h.renyi '' Ioi 1) ≤ r
  · exact hdone
  have hgap : r < sInf (h.renyi '' Ioi 1) := lt_of_not_ge hdone
  apply threshold_le_of_two_term_bound hBlt
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hell : sInf (h.renyi '' Ioi 1) <
      sInf (h.renyi '' Ioi 1) + 1 / (t * t) :=
    lt_add_of_pos_right _ (by positivity)
  have hhigh := high_rate_vanishing
    (fun n => h.testing_nonneg n _) hell
    (fun a ha haell n hn => h.renyi_testing a ha _ haell n hn)
  have hsqrt : Tendsto
      (fun n => Real.sqrt (h.testing n (sInf (h.renyi '' Ioi 1) + 1 / (t * t))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hhigh
  exact two_term_bound_of_three_piece
    (fun n => Real.sqrt_nonneg _) (fun n => Real.sqrt_nonneg _)
    hBevent hsqrt (h.three_piece r hr hgap t ht)

/-- The manuscript's exact threshold criterion, equation `thresholdcriterion`.
The upper bound one is explicit so real limsup cannot hide unbounded values. -/
theorem FiniteAnalyticInputs.threshold_criterion (h : FiniteAnalyticInputs)
    {r : ℝ} (hr : 0 ≤ r) (hupper : ∀ n, h.testing n r ≤ 1)
    (hlimsup : Filter.limsup (fun n => h.testing n r) atTop < 1) :
    sInf (h.renyi '' Ioi 1) ≤ r := by
  obtain ⟨B, _, hBlt, hBevent⟩ :=
    eventual_sqrt_bound_of_limsup_lt_one_of_le_one hupper hlimsup
  exact h.threshold_le_of_eventual_sqrt_bound hr hBlt hBevent

/-- The weak testing estimate supplies an eventual error below one at every
rate above `d`, so the finite thresholds coincide. -/
theorem FiniteAnalyticInputs.threshold_eq (h : FiniteAnalyticInputs) :
    sInf (h.renyi '' Ioi 1) = h.d := by
  apply threshold_eq_of_forall_gt (le_infimum_of_order_bounds h.relative_le_renyi)
  intro r hr
  have hrpos : 0 < r := lt_of_le_of_lt h.d_nonneg hr
  obtain ⟨B, _, hBlt, hBevent⟩ := eventual_sqrt_bound_of_weak_testing
    h.d_nonneg hr (h.weak_testing r hrpos)
  exact h.threshold_le_of_eventual_sqrt_bound hrpos.le hBlt hBevent

/-- The complete finite right-limit argument from the stated quantum bridge. -/
theorem FiniteAnalyticInputs.right_continuity (h : FiniteAnalyticInputs) :
    Tendsto h.renyi (𝓝[>] (1 : ℝ)) (𝓝 h.d) :=
  tendsto_right_of_threshold_eq h.order_mono h.relative_le_renyi h.threshold_eq



end ChannelContinuity
