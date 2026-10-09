/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import Quantum.QuantumEntropy.SandwichedRenyiUmegaki
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Concrete finite-dimensional quantum divergence foundations

The states and channels below are the actual positive operators and completely
positive trace-preserving maps from Lean-Quantum. All divergences use bits.
The extended-real definitions retain infinite values for support mismatch.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

universe u

variable {H K : Type u} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- A normalized positive quantum state, including singular states. -/
structure DensityState (H : Type u) [Qudit H] where
  op : L H
  nonneg : 0 ≤ op
  trace_one : Tr op = 1

namespace DensityState

@[ext] theorem ext {ρ σ : DensityState H} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

/-- Trace normalization makes every density operator nonzero. -/
theorem op_ne_zero (ρ : DensityState H) : ρ.op ≠ 0 := by
  intro h
  have := ρ.trace_one
  simp [h] at this

/-- CPTP maps act on the actual density operators and preserve normalization. -/
noncomputable def map (E : CPTP H K) (ρ : DensityState H) : DensityState K where
  op := E.toFun ρ.op
  nonneg := map_nonneg E.toCompletelyPositiveMap ρ.nonneg
  trace_one := (E.trace_map ρ.op).symm.trans ρ.trace_one

@[simp] theorem map_op (E : CPTP H K) (ρ : DensityState H) :
    (ρ.map E).op = E.toFun ρ.op := rfl

/-- The normalized identity operator, used for the discard-channel proof. -/
noncomputable def maximallyMixed (H : Type u) [Qudit H] [Nontrivial H] : DensityState H where
  op := (Module.finrank ℂ H : ℂ)⁻¹ • (1 : L H)
  nonneg := nonneg_of_pdSetLM (maxmixed_pdSetLM H)
  trace_one := by
    rw [map_smul, smul_eq_mul, LinearMap.trace_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')

/-- Discarding a normalized input always returns the maximally mixed state. -/
@[simp] theorem map_depolarizing (ρ : DensityState H) :
    ρ.map (depolarizingChannel H K) = maximallyMixed K := by
  apply ext
  change (Tr ρ.op / (Module.finrank ℂ K : ℂ)) • (1 : L K) = _
  simp [ρ.trace_one, maximallyMixed, one_div]

end DensityState

/-- Conversion from natural-log units to bits, with infinities preserved. -/
noncomputable def toBits (x : EReal) : EReal := ((Real.log 2)⁻¹ : ℝ) * x

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem toBits_mono : Monotone toBits := by
  intro x y h
  exact mul_le_mul_of_nonneg_left h (by
    exact_mod_cast (inv_nonneg.mpr log_two_pos.le))

@[simp] theorem toBits_coe (x : ℝ) : toBits (x : EReal) = (x / Real.log 2 : ℝ) := by
  unfold toBits
  rw [← EReal.coe_mul]
  congr 1
  ring

@[simp] theorem toBits_zero : toBits 0 = 0 := by simp [toBits]

@[simp] theorem toBits_top : toBits ⊤ = ⊤ := by
  exact EReal.mul_top_of_pos (by exact_mod_cast (inv_pos.mpr log_two_pos))

/-- The support-aware sandwiched Rényi divergence in bits.

Since `H` is finite dimensional, each operator in `L H` has finite spectrum and every
scalar function is continuous on that spectrum. Thus `CFC.rpow σ.op t` for `t < 0`
raises positive eigenvalues to `t` and sends zero eigenvalues to zero
(`NNReal.zero_rpow`), giving the pseudo-inverse power on the support of `σ.op`.
The separate support test in `sandwichedRenyiDivNN` assigns infinity when required. -/
noncomputable def stateRenyi (α : ℝ) (ρ σ : DensityState H) : EReal :=
  toBits (sandwichedRenyiDivNN α ρ.op σ.op)

/-- The support-aware Umegaki relative entropy in bits. -/
noncomputable def stateRelative (ρ σ : DensityState H) : EReal :=
  toBits (umegakiRelEntropyNN ρ.op σ.op)

/-- Concrete, support-aware data processing for every admissible Rényi order. -/
theorem stateRenyi_dataProcessing (E : CPTP H K) {α : ℝ}
    (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1) (ρ σ : DensityState H) :
    stateRenyi α (ρ.map E) (σ.map E) ≤ stateRenyi α ρ σ :=
  toBits_mono (sandwichedRenyiDivNN_monotone E hα hα1 ρ.nonneg σ.nonneg)

/-- Concrete Umegaki data processing, with singular states allowed. -/
theorem stateRelative_dataProcessing (E : CPTP H K) (ρ σ : DensityState H) :
    stateRelative (ρ.map E) (σ.map E) ≤ stateRelative ρ σ :=
  toBits_mono (umegakiRelEntropyNN_monotone E ρ.nonneg σ.nonneg)

/-- For orders above one, support mismatch gives genuine infinity. -/
theorem stateRenyi_eq_top_of_not_support {α : ℝ} (hα : 1 < α)
    (ρ σ : DensityState H) (hs : ¬ suppLE ρ.op σ.op) :
    stateRenyi α ρ σ = ⊤ := by
  simp [stateRenyi, sandwichedRenyiDivNN, hα, hs]

/-- Relative entropy has the same support-mismatch convention. -/
theorem stateRelative_eq_top_of_not_support (ρ σ : DensityState H)
    (hs : ¬ suppLE ρ.op σ.op) : stateRelative ρ σ = ⊤ := by
  simp [stateRelative, umegakiRelEntropyNN, hs]

/-- On the support region the concrete Rényi definition has the manuscript's
base-two formula, without a trace-normalization denominator. -/
theorem stateRenyi_eq_formula {α : ℝ} (hα : 1 < α) (ρ σ : DensityState H)
    (hs : suppLE ρ.op σ.op) :
    stateRenyi α ρ σ =
      ((1 / (α - 1)) * Real.logb 2 (sandwichedQuasi α ρ.op σ.op).re : ℝ) := by
  have hnot : ¬ α < 1 := not_lt.mpr hα.le
  simp only [stateRenyi, sandwichedRenyiDivNN, hs, not_true_eq_false, and_false,
    hnot, false_and, or_self, ↓reduceIte, toBits_coe]
  rw [sandwichedRenyiDiv, ρ.trace_one]
  simp only [Complex.one_re, div_one, Real.logb]
  congr 1
  ring

/-- The finite Umegaki formula for normalized states. -/
theorem stateRelative_eq_formula (ρ σ : DensityState H)
    (hs : suppLE ρ.op σ.op) :
    stateRelative ρ σ =
      ((Tr (ρ.op * (CFC.log ρ.op - CFC.log σ.op))).re / Real.log 2 : ℝ) := by
  simp [stateRelative, umegakiRelEntropyNN, hs, umegakiNorm, ρ.trace_one]

/-- Finiteness of relative entropy is exactly support inclusion. -/
theorem stateRelative_ne_top_iff (ρ σ : DensityState H) :
    stateRelative ρ σ ≠ ⊤ ↔ suppLE ρ.op σ.op := by
  constructor
  · intro h
    by_contra hs
    exact h (stateRelative_eq_top_of_not_support ρ σ hs)
  · intro hs
    rw [stateRelative_eq_formula ρ σ hs]
    exact EReal.coe_ne_top _

/-- For orders above one, Rényi finiteness has the same support criterion. -/
theorem stateRenyi_ne_top_iff {α : ℝ} (hα : 1 < α) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≠ ⊤ ↔ suppLE ρ.op σ.op := by
  constructor
  · intro h
    by_contra hs
    exact h (stateRenyi_eq_top_of_not_support hα ρ σ hs)
  · intro hs
    rw [stateRenyi_eq_formula hα ρ σ hs]
    exact EReal.coe_ne_top _

/-- Equality of the two arguments makes Umegaki relative entropy zero,
including at singular states. -/
@[simp] theorem stateRelative_self (ρ : DensityState H) : stateRelative ρ ρ = 0 := by
  have hs : suppLE ρ.op ρ.op := le_rfl
  simp [stateRelative, umegakiRelEntropyNN, hs, umegakiNorm]

/-- Equality of faithful arguments makes the Rényi divergence zero. -/
theorem stateRenyi_self_faithful {α : ℝ} (hα : 0 < α)
    (ρ : DensityState H) (hρ : ρ.op ∈ pdSetLM) : stateRenyi α ρ ρ = 0 := by
  have hs : suppLE ρ.op ρ.op := le_rfl
  have hQ := sandwichedQuasi_self_pdSetLM (ne_of_gt hα) hρ
  simp [stateRenyi, sandwichedRenyiDivNN, hs, sandwichedRenyiDiv,
    hQ, ρ.trace_one]

/-- Nonnegativity follows from an actual discard channel and data processing. -/
theorem stateRenyi_nonneg {α : ℝ} (hα : (1 : ℝ) / 2 ≤ α) (hα1 : α ≠ 1)
    (ρ σ : DensityState H) : 0 ≤ stateRenyi α ρ σ := by
  have h := stateRenyi_dataProcessing (depolarizingChannel H H) hα hα1 ρ σ
  have hz : stateRenyi α (DensityState.maximallyMixed H) (DensityState.maximallyMixed H) = 0 :=
    stateRenyi_self_faithful (by linarith) (DensityState.maximallyMixed H) (maxmixed_pdSetLM H)
  have hr := DensityState.map_depolarizing (K := H) ρ
  have hs := DensityState.map_depolarizing (K := H) σ
  rw [hr, hs, hz] at h
  exact h

/-- Nonnegativity of Umegaki relative entropy also includes singular states. -/
theorem stateRelative_nonneg (ρ σ : DensityState H) : 0 ≤ stateRelative ρ σ := by
  have h := stateRelative_dataProcessing (depolarizingChannel H H) ρ σ
  simpa only [DensityState.map_depolarizing, stateRelative_self] using h

/-- The order-one limit for faithful states in the exact base-two convention.
The singular-state extension of this limit is deliberately not claimed here. -/
theorem stateRenyi_tendsto_one_faithful (ρ σ : DensityState H)
    (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    Filter.Tendsto (fun α => stateRenyi α ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) := by
  have hs := suppLE_of_pdSetLM_right ρ.op hσ
  have hlim := (sandwichedRenyiDiv_tendsto_umegaki hρ hσ).div_const (Real.log 2)
  have hcoe := (continuous_coe_real_ereal.tendsto (umegakiNorm ρ.op σ.op / Real.log 2)).comp hlim
  have htarget : stateRelative ρ σ = (umegakiNorm ρ.op σ.op / Real.log 2 : ℝ) := by
    simp [stateRelative, umegakiRelEntropyNN, hs]
  rw [htarget]
  apply hcoe.congr'
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hnot : ¬ α < 1 := not_lt.mpr (le_of_lt hα)
  simp [stateRenyi, sandwichedRenyiDivNN, hs, hnot]

end QuantumChannelContinuity
