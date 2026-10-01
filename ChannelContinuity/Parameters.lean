/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import ChannelContinuity.ThreePiece

/-!
# Parameters and scalar normalization in the three-piece estimate

This file verifies the order choice `α = n / (n - t)` and the base-two
power algebra used to normalize the exponentiated Schatten bound.
-/

namespace ChannelContinuity

/-- The order chosen in the manuscript is strictly greater than one. -/
theorem renyi_order_gt_one {n t : ℝ} (ht : 0 < t) (htn : t < n) :
    1 < n / (n - t) := by
  apply (one_lt_div (sub_pos.mpr htn)).2
  linarith

/-- The near-one range suffices for the first limit: after `n ≥ 2t`, the
chosen Rényi order is at most two. -/
theorem renyi_order_le_two {n t : ℝ} (htn : t < n) (h2tn : 2 * t ≤ n) :
    n / (n - t) ≤ 2 := by
  apply (div_le_iff₀ (sub_pos.mpr htn)).2
  linarith

/-- The corresponding Schatten interpolation parameter is exactly `t / n`. -/
theorem renyi_order_fraction {n t : ℝ} (ht : 0 < t) (htn : t < n) :
    (n / (n - t) - 1) / (n / (n - t)) = t / n := by
  have hn : n ≠ 0 := ne_of_gt (lt_trans ht htn)
  have hnt : n - t ≠ 0 := ne_of_gt (sub_pos.mpr htn)
  field_simp
  ring

/-- The interpolation parameter lies strictly between zero and one. -/
theorem renyi_fraction_mem_Ioo {n t : ℝ} (ht : 0 < t) (htn : t < n) :
    t / n ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : 0 < n := lt_trans ht htn
  exact ⟨div_pos ht hn, (div_lt_one hn).2 htn⟩

/-- Raising a block-rate weight to `s/2`, with `s=t/n`, cancels the block size. -/
theorem block_rate_weight {n : ℝ} (hn : n ≠ 0) (t rate : ℝ) :
    ((2 : ℝ) ^ (n * rate)) ^ (t / n / 2) = (2 : ℝ) ^ (t * rate / 2) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  field_simp

/-- Dividing the cheaper piece by the threshold's exponential gives a negative
rate-gap factor. -/
theorem normalized_low_weight {n : ℝ} (hn : n ≠ 0) (t r dPlus : ℝ) :
    ((2 : ℝ) ^ (n * r)) ^ (t / n / 2) / (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (-t * (dPlus - r) / 2) := by
  rw [block_rate_weight hn, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The fixed multiplier four becomes the factor `2^(t/n)`. -/
theorem four_weight (n t : ℝ) :
    (4 : ℝ) ^ (t / n / 2) = (2 : ℝ) ^ (t / n) := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- General normalized weight for a piece with CP multiplier four. -/
theorem normalized_four_weight {n : ℝ} (hn : n ≠ 0) (t rate dPlus : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ (n * rate)) ^ (t / n / 2) /
        (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (t / n) * (2 : ℝ) ^ (t * (rate - dPlus) / 2) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg (by norm_num) _),
    four_weight, block_rate_weight hn, mul_div_assoc,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

/-- The higher approximation rate `dPlus+t⁻²` leaves only `2^(1/(2t))`. -/
theorem normalized_high_weight {n t : ℝ} (hn : n ≠ 0) (ht : t ≠ 0) (dPlus : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ (n * (dPlus + 1 / (t * t)))) ^ (t / n / 2) /
        (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (t / n) * (2 : ℝ) ^ (1 / (2 * t)) := by
  rw [normalized_four_weight hn]
  congr 2
  field_simp
  ring

/-- The exponentiated Schatten estimate with the three manuscript CP weights,
before division by the threshold factor. -/
noncomputable def rawSchattenRhs (n : ℕ) (t r dPlus cap b ε : ℝ) : ℝ :=
  (1 + b) ^ (1 - t / n) * ((2 : ℝ) ^ ((n : ℝ) * r)) ^ (t / n / 2) +
  (b + ε) ^ (1 - t / n) *
    ((4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (dPlus + 1 / (t * t)))) ^ (t / n / 2) +
  ε ^ (1 - t / n) *
    ((4 : ℝ) * (2 : ℝ) ^ ((n : ℝ) * (cap + 1))) ^ (t / n / 2)

/-- Exact normalization of all three terms, including both factors arising
from the fixed multiplier four. -/
theorem raw_schatten_normalization {n : ℕ} {t : ℝ}
    (hn : (n : ℝ) ≠ 0) (ht : t ≠ 0) (r dPlus cap b ε : ℝ) :
    rawSchattenRhs n t r dPlus cap b ε / (2 : ℝ) ^ (t * dPlus / 2) =
      threePieceRhs n t r dPlus cap b ε := by
  unfold rawSchattenRhs threePieceRhs
  rw [add_div, add_div,
    mul_div_assoc ((1 + b) ^ (1 - t / (n : ℝ))) _ _,
    mul_div_assoc ((b + ε) ^ (1 - t / (n : ℝ))) _ _,
    mul_div_assoc (ε ^ (1 - t / (n : ℝ))) _ _,
    normalized_low_weight hn, normalized_high_weight hn ht, normalized_four_weight hn]
  ring

/-- The raw three-term Schatten estimate implies the normalized inequality
used by the first limiting argument.  This step is scalar algebra only; the
raw operator-theoretic estimate remains an explicit hypothesis. -/
theorem three_piece_bound_of_raw_schatten {n : ℕ} {t r dPlus cap b ε : ℝ}
    (ht : 1 ≤ t) (htn : t < (n : ℝ))
    (hraw : (2 : ℝ) ^ (t * dPlus / 2) ≤ rawSchattenRhs n t r dPlus cap b ε) :
    1 ≤ threePieceRhs n t r dPlus cap b ε := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (lt_trans ht0 htn)
  have hden : 0 < (2 : ℝ) ^ (t * dPlus / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hdiv : 1 ≤ rawSchattenRhs n t r dPlus cap b ε / (2 : ℝ) ^ (t * dPlus / 2) :=
    (le_div_iff₀ hden).2 (by simpa using hraw)
  simpa [raw_schatten_normalization hn0 (ne_of_gt ht0)] using hdiv

end ChannelContinuity
