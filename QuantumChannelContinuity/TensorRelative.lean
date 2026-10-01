/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.ChannelProducts
import QuantumChannelContinuity.StateSupportLimits

/-! # Relative-entropy additivity from the proved singular-state order-one limit -/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal Topology

namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

variable {A B C D : Type} [Qudit A] [Qudit B] [Qudit C] [Qudit D]
  [Nontrivial A] [Nontrivial B] [Nontrivial C] [Nontrivial D]

/-- Tensor additivity of actual Umegaki relative entropy, including singular
states and infinite support mismatch, follows from the full state limit. -/
theorem stateRelative_tensor (ρ σ : DensityState A) (τ ω : DensityState B) :
    stateRelative (ρ.tensor τ) (σ.tensor ω) = stateRelative ρ σ + stateRelative τ ω := by
  have hr : Filter.Tendsto (fun p => stateRenyi p ρ σ) (𝓝[>] (1 : ℝ))
      (𝓝 (stateRelative ρ σ)) := (stateRenyi_tendsto_one ρ σ).mono_left
    (nhdsWithin_mono _ (fun _ h => ne_of_gt h))
  have ht : Filter.Tendsto (fun p => stateRenyi p τ ω) (𝓝[>] (1 : ℝ))
      (𝓝 (stateRelative τ ω)) := (stateRenyi_tendsto_one τ ω).mono_left
    (nhdsWithin_mono _ (fun _ h => ne_of_gt h))
  have hr0 : stateRelative ρ σ ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (stateRelative_nonneg ρ σ)
  have ht0 : stateRelative τ ω ≠ ⊥ :=
    ne_bot_of_le_ne_bot (by simp) (stateRelative_nonneg τ ω)
  have hadd := (EReal.continuousAt_add (Or.inr ht0) (Or.inl hr0)).tendsto.comp (hr.prodMk_nhds ht)
  have hprod : Filter.Tendsto (fun p => stateRenyi p (ρ.tensor τ) (σ.tensor ω))
      (𝓝[>] (1 : ℝ)) (𝓝 (stateRelative (ρ.tensor τ) (σ.tensor ω))) :=
    (stateRenyi_tendsto_one (ρ.tensor τ) (σ.tensor ω)).mono_left
    (nhdsWithin_mono _ (fun _ h => ne_of_gt h))
  apply tendsto_nhds_unique hprod
  apply hadd.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (stateRenyi_tensor hp ρ σ τ ω).symm

/-- Relative entropy of concrete stabilized channels is superadditive under
tensor products; all input and reference spaces are explicit. -/
theorem channelRelative_tensor_superadditive (N M : CPTP A B) (K L : CPTP C D) :
    channelRelative N M + channelRelative K L ≤
      channelRelative (tensorChannel N K) (tensorChannel M L) := by
  apply ENNReal.iSup_add_iSup_le
  intro ψ φ
  have h := stateRelative_le_channel (tensorChannel N K) (tensorChannel M L)
    (ψ.stabilizedProduct φ)
  rw [amplifiedOutput_product N K, amplifiedOutput_product M L,
    stateRelative_isometry, stateRelative_tensor,
    EReal.toENNReal_add (stateRelative_nonneg _ _) (stateRelative_nonneg _ _)] at h
  exact h

end QuantumChannelContinuity
