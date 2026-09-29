import QuantumChannelContinuity.ChannelDominationBounds
import QuantumChannelContinuity.StateSupportLimits
import QuantumChannelContinuity.RegularizationIdentities

/-!
# Complete finite/infinite classification and pointwise limits

The support dichotomy is connected to the actual block-supremum divergences.
Finiteness is equivalent to finite CP domination; infinite relative entropy
has a concrete one-use Choi witness and satisfies the whole continuity claim.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- Every concrete normalized block output has the required left limit. -/
theorem inputRenyi_tendsto_one_left (N M : CPTP H K) (i : BlockInput H) :
    Tendsto (fun α => inputRenyi N M α i) (𝓝[<] (1 : ℝ))
      (𝓝 (inputRelative N M i)) := by
  have hs := stateRenyi_tendsto_one_left
    (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)
  have he := (EReal.continuous_toENNReal.tendsto _).comp hs
  exact ENNReal.Tendsto.div_const he
    (Or.inr (by exact_mod_cast i.1.property.ne'))

/-- One actual support-mismatched input forces infinite regularized relative entropy. -/
theorem regularizedRelative_top_of_channel_support_mismatch (N M : CPTP H K)
    (ψ : PureInput (H ⊗[ℂ] H))
    (hs : ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op) :
    regularizedRelative N M = ⊤ := by
  apply top_unique
  simpa only [channelRelative_top_of_support_mismatch N M ψ hs] using
    channelRelative_le_regularized N M

/-- Finiteness of regularized relative entropy is exactly finite CP domination.
This supplies the finite/infinite case split without an external hypothesis. -/
theorem regularizedRelative_ne_top_iff_cp_domination (N M : CPTP H K) :
    regularizedRelative N M ≠ ⊤ ↔
      ∃ c : ℝ, 0 < c ∧ CPLe N.toLinearMap (c • M.toLinearMap) := by
  constructor
  · intro hfin
    rcases cp_domination_or_support_mismatch N M with hc | ⟨ψ, hψ⟩
    · exact hc
    · exact (hfin (regularizedRelative_top_of_channel_support_mismatch N M ψ hψ)).elim
  · rintro ⟨c, hc, hdom⟩
    exact (regularized_finite_of_cp_domination N M hc hdom).1

/-- Infinite regularized relative entropy has a genuine single-use support witness. -/
theorem channel_support_mismatch_of_regularizedRelative_top (N M : CPTP H K)
    (htop : regularizedRelative N M = ⊤) :
    ∃ ψ : PureInput (H ⊗[ℂ] H),
      ¬ suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op := by
  rcases cp_domination_or_support_mismatch N M with ⟨c, hc, hdom⟩ | hψ
  · exact ((regularized_finite_of_cp_domination N M hc hdom).1 htop).elim
  · exact hψ

/-- The full two-sided continuity conclusion whenever regularized relative
entropy is infinite. No witness, monotonicity, or filter premise is supplied. -/
theorem theorem_one_of_regularizedRelative_top (N M : CPTP H K)
    (htop : regularizedRelative N M = ⊤) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  obtain ⟨ψ, hs⟩ := channel_support_mismatch_of_regularizedRelative_top N M htop
  rw [htop, ← nhdsLT_sup_nhdsGT]
  apply Filter.Tendsto.sup
  · have hleft := stateRenyi_tendsto_top_left_of_not_support _ _ hs
    have he : Tendsto (fun α =>
        (stateRenyi α (amplifiedOutput N ψ.density) (amplifiedOutput M ψ.density)).toENNReal)
        (𝓝[<] (1 : ℝ)) (𝓝 ⊤) := by
      simpa only [EReal.toENNReal_top] using
        (EReal.continuous_toENNReal.tendsto ⊤).comp hleft
    apply tendsto_nhds_top_mono he
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)).filter_mono nhdsWithin_le_nhds]
      with α hα hαhalf
    exact (stateRenyi_le_channel N M α ψ).trans
      (channelRenyi_le_regularized hαhalf.le (ne_of_lt hα) N M)
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    apply Eq.symm
    apply top_unique
    simpa only [channelRenyi_top_of_support_mismatch N M ψ hα hs] using
      channelRenyi_le_regularized (by have hα' : 1 < α := hα; linarith) (ne_of_gt hα) N M

end QuantumChannelContinuity
