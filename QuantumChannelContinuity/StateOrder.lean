import QuantumChannelContinuity.StateOrderBoundary
import QuantumChannelContinuity.StateOrderRenyi

/-!
# Unconditional Rényi order monotonicity

Complex interpolation proves the faithful inequality. The proved density
approximation and data-processing argument extends it to singular states,
including the support-mismatch and zero-overlap infinity conventions.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
variable {H : Type} [Qudit H] [Nontrivial H]

/-- Rényi divergence is increasing with its order, across both sides of one.
The endpoints exclude one itself, where the expression is defined separately. -/
theorem stateRenyi_le_of_order {α β : ℝ} (hα : (1 : ℝ) / 2 < α)
    (hα1 : α ≠ 1) (hβ1 : β ≠ 1) (hαβ : α ≤ β) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  have hf : ∀ (τ ω : DensityState H), τ.op ∈ pdSetLM → ω.op ∈ pdSetLM →
      stateRenyi α τ ω ≤ stateRenyi β τ ω :=
    fun τ ω hτ hω => stateRenyi_le_of_faithful hα hα1 hβ1 hαβ τ ω hτ hω
  by_cases hl : α < 1
  · exact stateRenyi_le_of_faithful_lt (by linarith) hl (by linarith) hβ1 hf ρ σ
  · exact stateRenyi_le_of_faithful_gt (by rcases lt_or_gt_of_ne hα1 with h | h <;> linarith)
      hαβ hf ρ σ

/-- Monotonicity below one for arbitrary density states. -/
theorem stateRenyi_monotoneOn_left (ρ σ : DensityState H) :
    MonotoneOn (fun α => stateRenyi α ρ σ) (Ioo (1 / 2) 1) := by
  intro α hα β hβ hαβ
  exact stateRenyi_le_of_order hα.1 hα.2.ne hβ.2.ne hαβ ρ σ

/-- Monotonicity above one for arbitrary density states. -/
theorem stateRenyi_monotoneOn_right (ρ σ : DensityState H) :
    MonotoneOn (fun α => stateRenyi α ρ σ) (Ioi 1) := by
  intro α hα β hβ hαβ
  exact stateRenyi_le_of_order (by change 1 < α at hα; linarith)
    (ne_of_gt hα) (ne_of_gt hβ) hαβ ρ σ

/-- Above-one divergence bounds relative entropy, including infinity. -/
theorem stateRelative_le_stateRenyi {α : ℝ} (hα : 1 < α) (ρ σ : DensityState H) :
    stateRelative ρ σ ≤ stateRenyi α ρ σ := by
  have hlim := (stateRenyi_tendsto_one ρ σ).mono_left
    (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from fun _ h => ne_of_gt h))
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hα] with β hβ
  exact stateRenyi_monotoneOn_right ρ σ hβ.1 hα hβ.2.le

/-- Below-one divergence is bounded by relative entropy, including infinity. -/
theorem stateRenyi_le_stateRelative {α : ℝ} (hα : (1 : ℝ) / 2 < α) (hα1 : α < 1)
    (ρ σ : DensityState H) : stateRenyi α ρ σ ≤ stateRelative ρ σ := by
  apply ge_of_tendsto (stateRenyi_tendsto_one_left ρ σ)
  filter_upwards [Ioo_mem_nhdsLT hα1] with β hβ
  exact stateRenyi_monotoneOn_left ρ σ ⟨hα,hα1⟩ ⟨hα.trans hβ.1,hβ.2⟩ hβ.1.le

end QuantumChannelContinuity
