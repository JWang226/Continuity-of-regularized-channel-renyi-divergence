/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.TensorWords

/-!
# Exponential form of the actual regularized Schatten estimate

The block-supremum upper bound is converted into the manuscript's exponential
form.  Finiteness, support inclusion, and the lower bound on the sum of weights
are consequences of the supplied dilation decomposition.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- Scalar conversion of a logarithmic Rényi-rate upper bound. -/
theorem rpow_le_of_renyi_log_bound {p d z : ℝ} (hp : 1 < p) (hz : 0 < z)
    (hd : d ≤ (2 * p / (p - 1)) * Real.logb 2 z) :
    (2 : ℝ) ^ ((p - 1) / (2 * p) * d) ≤ z := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  calc
    _ ≤ (2 : ℝ) ^ ((p - 1) / (2 * p) * ((2 * p / (p - 1)) * Real.logb 2 z)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = (2 : ℝ) ^ Real.logb 2 z := by
      congr 1
      field_simp
    _ = z := Real.rpow_logb (by norm_num) (by norm_num) hz

/-- Extended-real version: a finite logarithmic upper bound gives finiteness
and the exponential estimate. The premise `1 ≤ z` handles the truncation in
`ENNReal.ofReal` explicitly. -/
theorem ennreal_rpow_le_of_renyi_log_bound {p z : ℝ} (hp : 1 < p) (hz : 1 ≤ z)
    (D : ℝ≥0∞) (hD : D ≤ ENNReal.ofReal ((2 * p / (p - 1)) * Real.logb 2 z)) :
    D ≠ ⊤ ∧ (2 : ℝ) ^ ((p - 1) / (2 * p) * D.toReal) ≤ z := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hz0 : 0 < z := zero_lt_one.trans_le hz
  have hlog : 0 ≤ Real.logb 2 z := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) zero_lt_one hz
  have hL : 0 ≤ (2 * p / (p - 1)) * Real.logb 2 z := by positivity
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD, ?_⟩
  apply rpow_le_of_renyi_log_bound hp hz0
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
  rwa [ENNReal.toReal_ofReal hL] at h

variable {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B] [Nontrivial E]

/-- The actual regularized channel divergence satisfies the exponential
filter–Schatten estimate. All tensor words and entangled inputs are accounted
for by the concrete tensor-power construction; finiteness is proved. -/
theorem regularizedRenyi_dilation_exponential_bound {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    regularizedRenyi p N M ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (regularizedRenyi p N M).toReal) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hchannel := channelRenyi_dilation_exponential_bound hp hp2 N M V hV U hVU
    b lam hb hlam hdom hnorm
  have hsum : 1 ≤ ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) :=
    (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2)
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)).trans hchannel.2
  exact ennreal_rpow_le_of_renyi_log_bound hp hsum (regularizedRenyi p N M)
    (regularizedRenyi_dilation_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm)

end QuantumChannelContinuity
