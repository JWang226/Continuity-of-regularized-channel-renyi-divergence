import QuantumChannelContinuity.SlackTraceBound
import QuantumChannelContinuity.FilterHockey

/-!
# Exact hockey-stick CP slack attainment

The closed semidefinite cone separates any infeasible target by an actual
positive Choi tester. Every such tester is bounded by the stabilized channel
hockey-stick divergence, which rules out separation at that exact value.
The Choi isomorphism then gives an attaining CP slack map. No optimization,
Slater, support, or attainability premise is used.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B]
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

/-- The exact CP-slack optimum is attained for every nonnegative threshold.
This is the previously missing Gour equation (44), stated directly in terms
of actual maps and the project's stabilized variational divergence. -/
theorem hockeySlackAttainment_of_nonneg (N M : CPTP A B) {γ : ℝ} (hγ : 0 ≤ γ) :
    HockeySlackAttainment γ N M := by
  classical
  let b := (stdOrthonormalBasis ℂ A).toBasis
  have hN : 0 ≤ choi b N.toLinearMap := cp_to_choi b _ ⟨N.toCompletelyPositiveMap,rfl⟩
  have hM : 0 ≤ (γ : ℂ) • choi b M.toLinearMap :=
    smul_nonneg (by exact_mod_cast hγ : (0 : ℂ) ≤ (γ : ℂ))
      (cp_to_choi b _ ⟨M.toCompletelyPositiveMap,rfl⟩)
  let D : Hermitian (B ⊗[ℂ] A) :=
    ⟨choi b N.toLinearMap - (γ : ℂ) • choi b M.toLinearMap,
      hN.isSelfAdjoint.sub hM.isSelfAdjoint⟩
  let ε := channelHockey γ N M
  have hprimal : ∃ Q : Hermitian (B ⊗[ℂ] A), 0 ≤ Q ∧ D ≤ Q ∧
      hermitianLeftTrace (A := A) (B := B) Q ≤ ε • (1 : Hermitian A) := by
    by_contra hno
    obtain ⟨W,Y,hW,hY,hle,hviol⟩ := choiSlack_separation D ε hno
    have htest := choi_test_le_hockey N M hγ (W : L (B ⊗[ℂ] A)) (Y : L A) hW hY hle
    exact (not_lt_of_ge htest) hviol
  obtain ⟨Q,hQ,hDQ,hτQ⟩ := hprimal
  obtain ⟨Φ,hΦ⟩ := choiLinear_surjective (B := B) b (Q : L (B ⊗[ℂ] A))
  have hΦchoi : choi b Φ = (Q : L (B ⊗[ℂ] A)) := hΦ
  have hΦcp : IsCompletelyPositive Φ := by
    apply choi_to_cp b
    change 0 ≤ choi b Φ
    rw [hΦchoi]
    exact hQ
  refine ⟨Φ,hΦcp,?_,?_⟩
  · apply (cpLe_iff_choi_le b _ _).mpr
    change choi b N.toLinearMap ≤ choiLinear b ((γ : ℂ) • M.toLinearMap + Φ)
    rw [map_add,map_smul,choiLinear_apply,choiLinear_apply,hΦchoi]
    exact (sub_le_iff_le_add').mp hDQ
  · intro a
    apply trace_le_of_choi_marginal Φ ε _ a
    rw [show (stdOrthonormalBasis ℂ A).toBasis = b from rfl,hΦchoi]
    change leftPartialTrace (Q : L (B ⊗[ℂ] A)) ≤ (ε : ℂ) • (1 : L A)
    change leftPartialTrace (Q : L (B ⊗[ℂ] A)) ≤ ε • (1 : L A) at hτQ
    simpa only [← algebraMap_smul ℂ ε (1 : L A)] using hτQ

/-- In particular, the exact slack exists on the manuscript's range γ ≥ 1. -/
theorem hockeySlackAttainment_of_one_le (N M : CPTP A B) {γ : ℝ} (hγ : 1 ≤ γ) :
    HockeySlackAttainment γ N M :=
  hockeySlackAttainment_of_nonneg N M (zero_le_one.trans hγ)

/-- The fixed-dilation hockey-stick filter with all existence and operator
steps proved, and no slack-attainment hypothesis. -/
theorem fixed_dilation_hockey_filter (N M : CPTP A B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (hV : dilationChannel V = N.toLinearMap)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] E,
      CPLe (dilationChannel W) ((γ : ℂ) • M.toLinearMap) ∧
      ‖(V-W).toContinuousLinearMap‖ ≤ Real.sqrt (channelHockey γ N M) :=
  fixed_dilation_hockey_filter_of_slack_attainment N M V hγ hV
    (hockeySlackAttainment_of_nonneg N M hγ)

end QuantumChannelContinuity
