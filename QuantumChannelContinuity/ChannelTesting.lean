/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.FoundationsWeakTesting

/-!
# Testing bounds for the actual stabilized channel divergences

The optimizations over both pure entangled inputs and all quantum effects
are discharged here. Only a bound on the channel divergence itself is used.
-/

open QuantumState QuantumChannel
open scoped ENNReal TensorProduct

namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- The exponential testing bound for concrete finite-dimensional channels. -/
theorem channelHockey_renyi_bound (N M : CPTP H K) {α ell a : ℝ}
    (hα : 1 < α) (ha : 0 ≤ a) (hD : channelRenyi α N M ≤ ENNReal.ofReal a) :
    channelHockey ((2 : ℝ) ^ ell) N M ≤ (2 : ℝ) ^ (-(α - 1) * (ell - a)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨ψ, rfl⟩
  exact stateHockey_renyi_bound _ _ hα
    (stateRenyi_le_of_channel_le N M (by linarith) (ne_of_gt hα) ha hD ψ)

/-- A block channel satisfying `Dα ≤ n*a` has the exact manuscript high-rate
bound. The block can be any actual CPTP map, including a tensor power. -/
theorem block_channelHockey_renyi_bound (N M : CPTP H K) (n : ℕ)
    {α ell a : ℝ} (hα : 1 < α) (ha : 0 ≤ a)
    (hD : channelRenyi α N M ≤ ENNReal.ofReal ((n : ℝ) * a)) :
    channelHockey ((2 : ℝ) ^ ((n : ℝ) * ell)) N M ≤
      (2 : ℝ) ^ (-(n : ℝ) * (α - 1) * (ell - a)) := by
  have h := channelHockey_renyi_bound N M (ell := (n : ℝ) * ell) hα
    (mul_nonneg (Nat.cast_nonneg n) ha) hD
  convert h using 1; congr 1; ring

/-- The weak testing bound for concrete stabilized channel relative entropy. -/
theorem channelHockey_relative_bound (N M : CPTP H K) {ell a : ℝ}
    (hell : 0 < ell) (ha : 0 ≤ a) (hD : channelRelative N M ≤ ENNReal.ofReal a) :
    channelHockey ((2 : ℝ) ^ ell) N M ≤ a / ell + 1 / ell := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨ψ, rfl⟩
  exact stateHockey_relative_bound _ _ hell
    (stateRelative_le_of_channel_le N M ha hD ψ)

/-- The exact block-size normalization of the concrete weak testing bound. -/
theorem block_channelHockey_relative_bound (N M : CPTP H K) {n : ℕ}
    (hn : 0 < n) {r d : ℝ} (hr : 0 < r) (hd : 0 ≤ d)
    (hD : channelRelative N M ≤ ENNReal.ofReal ((n : ℝ) * d)) :
    channelHockey ((2 : ℝ) ^ ((n : ℝ) * r)) N M ≤ d / r + 1 / ((n : ℝ) * r) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := channelHockey_relative_bound N M (mul_pos hnR hr)
    (mul_nonneg hnR.le hd) hD
  convert h using 1
  congr 1
  field_simp

end QuantumChannelContinuity
