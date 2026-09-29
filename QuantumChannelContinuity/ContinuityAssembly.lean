import QuantumChannelContinuity.FiniteInfinite
import QuantumChannelContinuity.SlackAttainment
import QuantumChannelContinuity.RegularizationLimits

/-!
# Assembly from order monotonicity

This intermediate module isolates order monotonicity as the final state-level
input. All state limits, support cases, CP caps, exact slack attainment, and
regularization identities are supplied by the preceding concrete proofs.
-/

open QuantumState QuantumChannel Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

theorem inputRenyi_tendsto_one_right (N M : CPTP H K) (i : BlockInput H) :
    Tendsto (fun α => inputRenyi N M α i) (𝓝[>] (1 : ℝ))
      (𝓝 (inputRelative N M i)) := by
  have hs := (stateRenyi_tendsto_one
    (amplifiedOutput (channelPower N i.1.val) i.2.density)
    (amplifiedOutput (channelPower M i.1.val) i.2.density)).mono_left
      (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from
        fun _ hx => ne_of_gt hx))
  exact ENNReal.Tendsto.div_const
    ((EReal.continuous_toENNReal.tendsto _).comp hs)
    (Or.inr (by exact_mod_cast i.1.property.ne'))

theorem inputRelative_le_inputRenyi_of_mono (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1))
    {α : ℝ} (hα : 1 < α) (i : BlockInput H) :
    inputRelative N M i ≤ inputRenyi N M α i := by
  apply le_of_tendsto (inputRenyi_tendsto_one_right N M i)
  filter_upwards [Ioo_mem_nhdsGT hα] with β hβ
  exact hmono i hβ.1 hα hβ.2.le

theorem regularizedRelative_le_regularizedRenyi_of_mono (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1))
    {α : ℝ} (hα : 1 < α) : regularizedRelative N M ≤ regularizedRenyi α N M := by
  rw [regularizedRelative_eq_input_sup, regularizedRenyi_eq_input_sup]
  exact iSup_mono (inputRelative_le_inputRenyi_of_mono N M hmono hα)

/-- Construct every finite threshold input from finite relative entropy and
actual state-order monotonicity. All operator and regularization fields are proved. -/
noncomputable def quantumThresholdInputs_of_mono (N M : CPTP H K)
    (hfin : regularizedRelative N M ≠ ⊤)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1)) :
    QuantumThresholdInputs N M := by
  let hex := (regularizedRelative_ne_top_iff_cp_domination N M).mp hfin
  let c := Classical.choose hex
  have hc := (Classical.choose_spec hex).1
  have hdom := (Classical.choose_spec hex).2
  have hf := (regularized_finite_of_cp_domination N M hc hdom).2
  let hcapex := finite_cap_of_cp_domination N M hc hdom
  let cap := Classical.choose hcapex
  have hcap := (Classical.choose_spec hcapex).1
  have hblock := (Classical.choose_spec hcapex).2
  exact {
    relative_finite := hfin
    renyi_finite := hf
    order_mono := by
      intro α hα β hβ hαβ
      apply ENNReal.toReal_mono (hf β hβ)
      simp_rw [regularizedRenyi_eq_input_sup]
      exact iSup_mono fun i => hmono i hα hβ hαβ
    relative_le_renyi := fun α hα => ENNReal.toReal_mono (hf α hα)
      (regularizedRelative_le_regularizedRenyi_of_mono N M hmono hα)
    cap := cap
    threshold_le_cap := hcap
    block_cap := hblock
    block_slack := fun n γ hγ =>
      hockeySlackAttainment_of_one_le (channelPower N n) (channelPower M n) hγ
    power_scaling := fun α hα _ n hn => regularizedRenyi_power_scaling hα N M hn }

/-- The open interval suffices for the left limit, avoiding any need to
include the endpoint α = 1/2 in the order-monotonicity statement. -/
theorem regularizedRenyi_tendsto_one_left_of_mono (N M : CPTP H K)
    (hmono : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1)) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[<] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  have hle {α : ℝ} (hα : α ∈ Ioo (1 / 2) 1) (i : BlockInput H) :
      inputRenyi N M α i ≤ inputRelative N M i := by
    apply ge_of_tendsto (inputRenyi_tendsto_one_left N M i)
    filter_upwards [Ioo_mem_nhdsLT hα.2] with β hβ
    exact hmono i hα ⟨hα.1.trans hβ.1, hβ.2⟩ hβ.1.le
  simp_rw [regularizedRenyi_eq_input_sup, regularizedRelative_eq_input_sup]
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp hb
    filter_upwards [(tendsto_order.mp (inputRenyi_tendsto_one_left N M i)).1 b hi]
      with α hα
    exact hα.trans_le (le_iSup (inputRenyi N M α) i)
  · intro b hb
    filter_upwards [Ioo_mem_nhdsLT (show (1 / 2 : ℝ) < 1 by norm_num)] with α hα
    exact (iSup_le fun i => (hle hα i).trans
      (le_iSup (inputRelative N M) i)).trans_lt hb

/-- All finite and infinite cases assembled, with only pointwise state-order
monotonicity left to instantiate in the final module. -/
theorem theorem_one_of_input_order (N M : CPTP H K)
    (hleft : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioo (1 / 2) 1))
    (hright : ∀ i : BlockInput H,
      MonotoneOn (fun α => inputRenyi N M α i) (Ioi 1)) :
    Tendsto (fun α => regularizedRenyi α N M) (𝓝[≠] (1 : ℝ))
      (𝓝 (regularizedRelative N M)) := by
  by_cases hfin : regularizedRelative N M = ⊤
  · exact theorem_one_of_regularizedRelative_top N M hfin
  · rw [← nhdsLT_sup_nhdsGT]
    exact (regularizedRenyi_tendsto_one_left_of_mono N M hleft).sup
      (regularized_right_continuity_from_quantum_inputs
        (quantumThresholdInputs_of_mono N M hfin hright))

end QuantumChannelContinuity
