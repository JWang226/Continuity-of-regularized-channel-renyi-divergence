/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# The first limit in the three-piece argument

This file proves the real-analysis passage from equation `threepiecebound` to
equation `contradiction` in the supplied manuscript.  The operator-theoretic
three-piece estimate is a hypothesis, not an axiom or a proved quantum fact.

An eventual bound `b n ≤ B < 1` replaces a limsup.  Continuity of real powers
at exponent one also covers zero bases, so no nonzero-error assumption is used.
-/

open Filter Topology

namespace ChannelContinuity

/-- Right-hand side of the paper's normalized three-piece estimate. -/
noncomputable def threePieceRhs (n : ℕ) (t r dPlus cap b ε : ℝ) : ℝ :=
  (1 + b) ^ (1 - t / n) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
  (2 : ℝ) ^ (t / n) * (b + ε) ^ (1 - t / n) * (2 : ℝ) ^ (1 / (2 * t)) +
  (2 : ℝ) ^ (t / n) * ε ^ (1 - t / n) *
    (2 : ℝ) ^ (t * (cap + 1 - dPlus) / 2)

/-- Fix `t`, then send the block length to infinity.  No uniform convergence
in `t` is required. -/
theorem two_term_bound_of_three_piece
    {b ε : ℕ → ℝ} {B t r dPlus cap : ℝ}
    (hb : ∀ n, 0 ≤ b n) (hε : ∀ n, 0 ≤ ε n)
    (hB : ∀ᶠ n in atTop, b n ≤ B)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop,
      1 ≤ threePieceRhs n t r dPlus cap (b n) (ε n)) :
    1 ≤ (1 + B) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
      B * (2 : ℝ) ^ (1 / (2 * t)) := by
  have hδ := tendsto_const_div_atTop_nhds_zero_nat t
  have hpow : Tendsto (fun n : ℕ => 1 - t / (n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hδ
  have hfirst : Tendsto (fun n : ℕ => (1 + B) ^ (1 - t / (n : ℝ)))
      atTop (𝓝 (1 + B)) := by
    simpa using (tendsto_const_nhds.rpow hpow (Or.inr (by norm_num : (0 : ℝ) < 1)))
  have hsecond : Tendsto (fun n : ℕ => (B + ε n) ^ (1 - t / (n : ℝ)))
      atTop (𝓝 B) := by
    simpa using ((tendsto_const_nhds.add hεlim).rpow hpow
      (Or.inr (by norm_num : (0 : ℝ) < 1)))
  have hthird : Tendsto (fun n : ℕ => ε n ^ (1 - t / (n : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hεlim.rpow hpow (Or.inr (by norm_num : (0 : ℝ) < 1)))
  have htwo : Tendsto (fun n : ℕ => (2 : ℝ) ^ (t / (n : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.rpow hδ
      (Or.inl (by norm_num : (2 : ℝ) ≠ 0)))
  have hlim : Tendsto (fun n => threePieceRhs n t r dPlus cap B (ε n)) atTop
      (𝓝 ((1 + B) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
        B * (2 : ℝ) ^ (1 / (2 * t)))) := by
    simpa [threePieceRhs] using
      ((hfirst.mul_const ((2 : ℝ) ^ (-t * (dPlus - r) / 2))).add
        ((htwo.mul hsecond).mul_const ((2 : ℝ) ^ (1 / (2 * t))))).add
        ((htwo.mul hthird).mul_const ((2 : ℝ) ^ (t * (cap + 1 - dPlus) / 2)))
  apply ge_of_tendsto hlim
  have hexp : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 - t / (n : ℝ) :=
    (hpow.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)
  filter_upwards [hbound, hB, hexp] with n hn hnB hnexp
  apply hn.trans
  unfold threePieceRhs
  apply add_le_add _ le_rfl
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by linarith [hb n]) (add_le_add le_rfl hnB) hnexp)
      (Real.rpow_nonneg (by norm_num) _)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (add_nonneg (hb n) (hε n))
          (add_le_add hnB le_rfl) hnexp)
        (Real.rpow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (by norm_num) _)

/-- The weak testing bound supplies a fixed eventual square-root error below
one at every rate above the relative entropy. -/
theorem eventual_sqrt_bound_of_weak_testing
    {E : ℕ → ℝ} {d r : ℝ} (hd : 0 ≤ d) (hdr : d < r)
    (hweak : ∀ n : ℕ, 0 < n → E n ≤ d / r + 1 / ((n : ℝ) * r)) :
    ∃ B : ℝ, 0 ≤ B ∧ B < 1 ∧ ∀ᶠ n in atTop, Real.sqrt (E n) ≤ B := by
  have hr : 0 < r := lt_of_le_of_lt hd hdr
  have hratio : d / r < 1 := (div_lt_one hr).2 hdr
  have hsqrt : Real.sqrt (d / r) < 1 := by
    have := Real.sq_sqrt (div_nonneg hd hr.le)
    have := Real.sqrt_nonneg (d / r)
    nlinarith
  obtain ⟨B, hB0, hB1⟩ := exists_between hsqrt
  refine ⟨B, (Real.sqrt_nonneg _).trans hB0.le, hB1, ?_⟩
  have hrem : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * r)) atTop (𝓝 (0 : ℝ)) := by
    simpa [div_div, mul_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 / r))
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (d / r + 1 / ((n : ℝ) * r)))
      atTop (𝓝 (Real.sqrt (d / r))) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tendsto_const_nhds.add hrem)
  filter_upwards [hlim.eventually (gt_mem_nhds hB0), eventually_gt_atTop 0]
    with n hn hn0
  exact (Real.sqrt_le_sqrt (hweak n hn0)).trans hn.le

end ChannelContinuity
