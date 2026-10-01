/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.PowerRegrouping
import QuantumChannelContinuity.TensorRelative
import QuantumChannelContinuity.RegularizationSup

/-!
# Superadditivity and exact block scaling of concrete regularization

The identities concern the actual tensor powers and the actual stabilized
channel divergences. Their proof uses product inputs, canonical Hilbert-space
regrouping, and the extended-real supremum argument.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

/-- The stabilized Rényi block sequence is superadditive, including infinities. -/
theorem blockRenyi_superadditive {p : ℝ} (hp : 1 < p) (N M : CPTP A B) (m n : ℕ) :
    blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (m + n) := by
  have h := channelRenyi_tensor_superadditive hp
    (channelPower N m) (channelPower M m) (channelPower N n) (channelPower M n)
  have heq := channelRenyi_isometry (by linarith : 1 / 2 ≤ p) hp.ne'
    (powerConcatIso A m n) (powerConcatIso B m n)
    (tensorChannel (channelPower N m) (channelPower N n))
    (tensorChannel (channelPower M m) (channelPower M n))
    (channelPower N (n + m)) (channelPower M (n + m))
    (powerConcat_intertwine N m n) (powerConcat_intertwine M m n)
  rw [heq] at h
  change blockRenyi p N M m + blockRenyi p N M n ≤ blockRenyi p N M (n + m) at h
  rwa [Nat.add_comm n m] at h

theorem blockRelative_superadditive (N M : CPTP A B) (m n : ℕ) :
    blockRelative N M m + blockRelative N M n ≤ blockRelative N M (m + n) := by
  have h := channelRelative_tensor_superadditive
    (channelPower N m) (channelPower M m) (channelPower N n) (channelPower M n)
  have heq := channelRelative_isometry
    (powerConcatIso A m n) (powerConcatIso B m n)
    (tensorChannel (channelPower N m) (channelPower N n))
    (tensorChannel (channelPower M m) (channelPower M n))
    (channelPower N (n + m)) (channelPower M (n + m))
    (powerConcat_intertwine N m n) (powerConcat_intertwine M m n)
  rw [heq] at h
  change blockRelative N M m + blockRelative N M n ≤ blockRelative N M (n + m) at h
  rwa [Nat.add_comm n m] at h

/-- Exact regularized Rényi block scaling. This is unconditional for every
order above one and every positive block length. -/
theorem regularizedRenyi_power_scaling {p : ℝ} (hp : 1 < p) (N M : CPTP A B)
    {n : ℕ} (hn : 0 < n) :
    regularizedRenyi p (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRenyi p N M := by
  simp only [regularizedRenyi, blockRenyi_power (by linarith : 1 / 2 ≤ p) hp.ne']
  exact ennreal_iSup_div_multiples (blockRenyi p N M) (blockRenyi_superadditive hp N M) hn

/-- Exact regularized relative-entropy block scaling. -/
theorem regularizedRelative_power_scaling (N M : CPTP A B) {n : ℕ} (hn : 0 < n) :
    regularizedRelative (channelPower N n) (channelPower M n) =
      (n : ℝ≥0∞) * regularizedRelative N M := by
  simp only [regularizedRelative, blockRelative_power]
  exact ennreal_iSup_div_multiples (blockRelative N M) (blockRelative_superadditive N M) hn

theorem channelRenyi_le_regularized {p : ℝ} (hp : 1 / 2 ≤ p) (hp1 : p ≠ 1)
    (N M : CPTP A B) : channelRenyi p N M ≤ regularizedRenyi p N M := by
  have h := blockRenyi_le_regularized p N M (n := 1) zero_lt_one
  simpa only [blockRenyi_one hp hp1, Nat.cast_one, mul_one] using h

theorem channelRelative_le_regularized (N M : CPTP A B) :
    channelRelative N M ≤ regularizedRelative N M := by
  have h := blockRelative_le_regularized N M (n := 1) zero_lt_one
  simpa only [blockRelative_one, Nat.cast_one, mul_one] using h

end QuantumChannelContinuity
