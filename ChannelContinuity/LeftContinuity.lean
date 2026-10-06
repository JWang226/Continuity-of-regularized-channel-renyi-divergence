/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.NormNum

/-!
# The left-hand and infinite-value parts of Theorem 1

An index `i : ι` stands for a block length together with an admissible input.
`f a i` is its normalized state Rényi divergence; `D i` is its normalized
relative entropy.  These are extended nonnegative reals, so the statements
include support mismatch and infinite regularized divergence.

The matrix definitions and the state-level facts are explicit hypotheses.
No quantum-information result is postulated as a Lean axiom.
-/

open Filter Set
open scoped Topology ENNReal

namespace ChannelContinuity

/-- The allowed orders to the left of one, including the endpoint one half. -/
def LeftOrders : Set ℝ := Ico (1 / 2) 1

variable {ι : Type*} {f : ℝ → ι → ℝ≥0∞} {D : ι → ℝ≥0∞}

/-- Pointwise monotonicity and convergence bound each order below the limiting
relative entropy.  The conclusion is valid also when `D i = ∞`. -/
theorem state_le_left_limit
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i)))
    {a : ℝ} (ha : a ∈ LeftOrders) (i : ι) : f a i ≤ D i := by
  apply ge_of_tendsto (hstate i)
  filter_upwards [Ioo_mem_nhdsLT ha.2] with b hb
  exact hmono i ha ⟨ha.1.trans hb.1.le, hb.2⟩ hb.1.le

/-- The left limit of a normalized state divergence is its supremum over
orders between one half and one. -/
theorem state_left_iSup_eq
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i)))
    (i : ι) : (⨆ a : LeftOrders, f a i) = D i := by
  apply le_antisymm
  · exact iSup_le fun a => state_le_left_limit hmono hstate a.property i
  · apply le_of_tendsto (hstate i)
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with a ha
    exact le_iSup (fun a : LeftOrders => f a i) ⟨a, ha.1.le, ha.2⟩

/-- The interchange of the order supremum with the block/input supremum in
Section 2 of the manuscript.  No finiteness of either supremum is needed. -/
theorem left_iSup_interchange
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i))) :
    (⨆ a : LeftOrders, ⨆ i, f a i) = ⨆ i, D i := by
  rw [iSup_comm]
  exact iSup_congr fun i => state_left_iSup_eq hmono hstate i

/-- Left continuity survives optimization over every block length and input.
This is an actual limit in `ℝ≥0∞`, including the infinite-value case. -/
theorem regularized_left_continuity
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i))) :
    Tendsto (fun a => ⨆ i, f a i) (𝓝[<] (1 : ℝ)) (𝓝 (⨆ i, D i)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp hb
    filter_upwards [(tendsto_order.mp (hstate i)).1 b hi] with a ha
    exact ha.trans_le (le_iSup (fun i => f a i) i)
  · intro b hb
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with a ha
    exact (iSup_le fun i => (state_le_left_limit hmono hstate ⟨ha.1.le, ha.2⟩ i).trans
      (le_iSup D i)).trans_lt hb

/-- One input with infinite divergence forces the optimized divergence to be
infinite.  In the manuscript this input is a maximally entangled state. -/
theorem regularized_eq_top_of_witness (g : ι → ℝ≥0∞) {i : ι}
    (hi : g i = ⊤) : (⨆ j, g j) = ⊤ := by
  apply top_unique
  simpa only [hi] using le_iSup g i

/-- An infinite regularized relative entropy gives right continuity from the
usual lower bound at every order above one, even without a single input
attaining infinite divergence. -/
theorem regularized_right_continuity_of_top
    (hD : (⨆ i, D i) = ⊤)
    (hlower : ∀ a > (1 : ℝ), ∀ i, D i ≤ f a i) :
    Tendsto (fun a => ⨆ i, f a i) (𝓝[>] (1 : ℝ)) (𝓝 (⨆ i, D i)) := by
  rw [hD]
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have hle : (⨆ i, D i) ≤ ⨆ i, f a i := iSup_mono (hlower a ha)
  rw [hD] at hle
  exact (top_unique hle).symm

/-- The right-hand limit in the support-mismatch case, stated with the
support implication made explicit as the witness hypotheses. -/
theorem regularized_right_continuity_of_infinite_witness
    (i : ι) (hD : D i = ⊤) (hf : ∀ a > (1 : ℝ), f a i = ⊤) :
    Tendsto (fun a => ⨆ j, f a j) (𝓝[>] (1 : ℝ)) (𝓝 (⨆ j, D j)) := by
  have htop : (⨆ j, D j) = ⊤ := regularized_eq_top_of_witness D hD
  rw [htop]
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (regularized_eq_top_of_witness (f a) (hf a ha)).symm

/-- Assembly of the two one-sided limits into the punctured limit used in
Theorem 1.  The Rényi divergence need not be defined meaningfully at order one. -/
theorem regularized_continuity_of_right_continuity
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i)))
    (hright : Tendsto (fun a => ⨆ i, f a i) (𝓝[>] (1 : ℝ)) (𝓝 (⨆ i, D i))) :
    Tendsto (fun a => ⨆ i, f a i) (𝓝[≠] (1 : ℝ)) (𝓝 (⨆ i, D i)) := by
  rw [← nhdsLT_sup_nhdsGT]
  exact (regularized_left_continuity hmono hstate).sup hright

/-- The full two-sided conclusion of Theorem 1 in the infinite witness case. -/
theorem regularized_continuity_of_infinite_witness
    (hmono : ∀ i, MonotoneOn (fun a => f a i) LeftOrders)
    (hstate : ∀ i, Tendsto (fun a => f a i) (𝓝[<] (1 : ℝ)) (𝓝 (D i)))
    (i : ι) (hD : D i = ⊤) (hf : ∀ a > (1 : ℝ), f a i = ⊤) :
    Tendsto (fun a => ⨆ j, f a j) (𝓝[≠] (1 : ℝ)) (𝓝 (⨆ j, D j)) :=
  regularized_continuity_of_right_continuity hmono hstate
    (regularized_right_continuity_of_infinite_witness i hD hf)

end ChannelContinuity
