import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic

/-!
# The scalar threshold argument

This file formalizes the final real-analysis step in the proof of Theorem 1.
The two-term inequality is the manuscript's equation `eq:contradiction`.
All limits here are proved in Lean; quantum-information input is not postulated
as an axiom and appears explicitly as hypotheses where needed.
-/

open Filter Set
open scoped Topology

namespace ChannelContinuity

/-- When there is a positive rate gap, the cheaper approximation's exponential
factor vanishes as the auxiliary real parameter tends to infinity. -/
theorem tendsto_two_rpow_neg_gap {dPlus r : ℝ} (hgap : r < dPlus) :
    Tendsto (fun t : ℝ => (2 : ℝ) ^ (-t * (dPlus - r) / 2)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => (-(dPlus - r) / 2) * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hexp := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp hlin
  apply hexp.congr
  intro t
  change (2 : ℝ) ^ (-(dPlus - r) / 2 * t) = (2 : ℝ) ^ (-t * (dPlus - r) / 2)
  congr 1
  ring

/-- The small upward perturbation of the higher threshold disappears. -/
theorem tendsto_two_rpow_inv_two_mul :
    Tendsto (fun t : ℝ => (2 : ℝ) ^ (1 / (2 * t))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun t : ℝ => 1 / (2 * t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_inv_atTop_zero.const_mul (1 / 2 : ℝ)).congr
      (fun t => by simp [div_eq_mul_inv, mul_inv_rev, mul_comm])
  have hpow := (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousAt.tendsto.comp hinv
  simpa using hpow

/-- Any exponential with a strictly positive rate vanishes along block sizes. -/
theorem tendsto_two_rpow_neg_nat_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) * c)) atTop (𝓝 0) := by
  have h := (tendsto_two_rpow_neg_gap (dPlus := 2 * c) (r := 0)
    (by linarith)).comp tendsto_natCast_atTop_atTop
  apply h.congr
  intro n
  change (2 : ℝ) ^ (-(n : ℝ) * (2 * c - 0) / 2) = (2 : ℝ) ^ (-(n : ℝ) * c)
  congr 1
  ring

/-- The high-rate testing estimate implies vanishing at every rate strictly
above the infimum of the order divergences. This is equation `eq:high` used at
`ell > dPlus`; the choice of a suitable order follows from the infimum property. -/
theorem high_rate_vanishing {E : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (hnonneg : ∀ n, 0 ≤ E n ell)
    (hell : sInf (f '' Ioi 1) < ell)
    (htesting : ∀ a : ℝ, 1 < a → f a < ell → ∀ n : ℕ, 0 < n →
      E n ell ≤ (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - f a))) :
    Tendsto (fun n => E n ell) atTop (𝓝 0) := by
  have hne : (f '' Ioi (1 : ℝ)).Nonempty := ⟨f 2, 2, by norm_num, rfl⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, hfa⟩ := exists_lt_of_csInf_lt hne hell
  have hdecay : Tendsto
      (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - f a)))
      atTop (𝓝 0) := by
    simpa only [mul_assoc] using
      (tendsto_two_rpow_neg_nat_mul (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hfa)))
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ hdecay
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact htesting a ha hfa n (by omega)

/-- The manuscript's last limit, with no uniformity in the earlier block-size
limit assumed: only the already-established inequality at each fixed `t` is used. -/
theorem threshold_le_of_two_term_bound {dPlus r b : ℝ} (hb : b < 1)
    (hbound : ∀ t : ℝ, 1 ≤ t →
      1 ≤ (1 + b) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
        b * (2 : ℝ) ^ (1 / (2 * t))) :
    dPlus ≤ r := by
  by_contra h
  have hgap : r < dPlus := lt_of_not_ge h
  have hlim : Tendsto (fun t : ℝ =>
      (1 + b) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
        b * (2 : ℝ) ^ (1 / (2 * t))) atTop (𝓝 b) := by
    simpa using ((tendsto_two_rpow_neg_gap hgap).const_mul (1 + b)).add
      (tendsto_two_rpow_inv_two_mul.const_mul b)
  have hb' : 1 ≤ b := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht using hbound t ht)
  exact (not_le_of_gt hb) hb'

/-- A threshold below every rate above `d`, and bounded below by `d`, equals `d`.
This is the last order-theoretic step of the proof. -/
theorem threshold_eq_of_forall_gt {d dPlus : ℝ} (hlower : d ≤ dPlus)
    (hupper : ∀ r : ℝ, d < r → dPlus ≤ r) : dPlus = d := by
  apply le_antisymm _ hlower
  by_contra h
  have hgap : d < dPlus := lt_of_not_ge h
  have := hupper ((d + dPlus) / 2) (by linarith)
  linarith

/-- Combine the scalar amplification contradiction at every rate above `d`
with the known lower bound. The weak testing estimate and operator lemmas
must supply the explicit `hbound` hypothesis. -/
theorem threshold_eq_of_bounds {d dPlus : ℝ} (hlower : d ≤ dPlus)
    (hbound : ∀ r : ℝ, d < r → ∃ b : ℝ, b < 1 ∧
      ∀ t : ℝ, 1 ≤ t →
        1 ≤ (1 + b) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
          b * (2 : ℝ) ^ (1 / (2 * t))) :
    dPlus = d := by
  apply threshold_eq_of_forall_gt hlower
  intro r hr
  obtain ⟨b, hb, h⟩ := hbound r hr
  exact threshold_le_of_two_term_bound hb h

/-- A monotone real-valued order divergence converges from the right to its
infimum. This includes the bounded finite-max-relative-entropy case. -/
theorem tendsto_right_to_infimum {f : ℝ → ℝ} {d : ℝ}
    (hmono : MonotoneOn f (Ioi 1)) (hlower : ∀ a : ℝ, 1 < a → d ≤ f a) :
    Tendsto f (𝓝[>] 1) (𝓝 (sInf (f '' Ioi 1))) := by
  apply hmono.tendsto_nhdsGT
  refine ⟨d, ?_⟩
  rintro y ⟨a, ha, rfl⟩
  exact hlower a ha

/-- Right continuity follows after identification of the infimum threshold. -/
theorem tendsto_right_of_threshold_eq {f : ℝ → ℝ} {d : ℝ}
    (hmono : MonotoneOn f (Ioi 1)) (hlower : ∀ a : ℝ, 1 < a → d ≤ f a)
    (hthreshold : sInf (f '' Ioi 1) = d) :
    Tendsto f (𝓝[>] 1) (𝓝 d) := by
  simpa [hthreshold] using tendsto_right_to_infimum hmono hlower

/-- A lower bound valid at every order also bounds the finite right threshold. -/
theorem le_infimum_of_order_bounds {f : ℝ → ℝ} {d : ℝ}
    (hlower : ∀ a : ℝ, 1 < a → d ≤ f a) :
    d ≤ sInf (f '' Ioi 1) := by
  apply le_csInf
  · exact ⟨f 2, 2, by norm_num, rfl⟩
  · rintro y ⟨a, ha, rfl⟩
    exact hlower a ha

/-- The finite scalar right-continuity theorem, conditional only on monotonicity,
the elementary lower bound, and the explicitly displayed two-term estimate. -/
theorem tendsto_right_of_two_term_bounds {f : ℝ → ℝ} {d : ℝ}
    (hmono : MonotoneOn f (Ioi 1)) (hlower : ∀ a : ℝ, 1 < a → d ≤ f a)
    (hbound : ∀ r : ℝ, d < r → ∃ b : ℝ, b < 1 ∧
      ∀ t : ℝ, 1 ≤ t →
        1 ≤ (1 + b) * (2 : ℝ) ^ (-t * (sInf (f '' Ioi 1) - r) / 2) +
          b * (2 : ℝ) ^ (1 / (2 * t))) :
    Tendsto f (𝓝[>] 1) (𝓝 d) := by
  exact tendsto_right_of_threshold_eq hmono hlower
    (threshold_eq_of_bounds (le_infimum_of_order_bounds hlower) hbound)

end ChannelContinuity
