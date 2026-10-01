/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.FilterSlack
import QuantumChannelContinuity.HockeyStick

/-!
# The CP-slack interface for the hockey-stick filter

`HockeySlackAttainment` states the existence part of Gour equation (44) in
terms of actual completely positive maps and pure-input traces.  It is an
explicit proposition, proved unconditionally for nonnegative thresholds in
`SlackAttainment`. The theorem below composes it with the prescribed-dilation
operator construction in `FilterSlack`.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]

theorem cp_smul_nonneg {Φ : QuantumChannel.T A B}
    (hΦ : IsCompletelyPositive Φ) {γ : ℝ} (hγ : 0 ≤ γ) :
    IsCompletelyPositive ((γ : ℂ) • Φ) := by
  let U : L B := (Real.sqrt γ : ℂ) • LinearMap.id
  have hU : LinearMap.adjoint U = U := by
    dsimp only [U]
    rw [map_smulₛₗ]
    simp
  have heq : (γ : ℂ) • Φ = (krausTerm U).comp Φ := by
    ext1 X
    change (γ : ℂ) • Φ X = U.comp ((Φ X).comp (LinearMap.adjoint U))
    rw [hU]
    ext1 x
    simp only [U, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_smul, smul_smul]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hγ]
  rw [heq]
  exact comp_isCompletelyPositive Φ (krausTerm U) hΦ (krausTerm_isCompletelyPositive U)

variable [Nontrivial A] [Nontrivial B]

/-- The exact SDP attainment assertion: a CP upper slack for `N - γ M`
whose trace effect is bounded by the stabilized testing optimum. -/
def HockeySlackAttainment (γ : ℝ) (N M : CPTP A B) : Prop :=
  ∃ Q : QuantumChannel.T A B,
    IsCompletelyPositive Q ∧
    CPLe N.toLinearMap ((γ : ℂ) • M.toLinearMap + Q) ∧
    ∀ a : A, (Tr (Q (outer_product a a))).re ≤ channelHockey γ N M * ‖a‖ ^ 2

/-- The manuscript's fixed-dilation hockey-stick filter, conditional only on
the exact slack-attainment assertion.  The Stinespring, ordered-CP,
environment alignment, square-root, and norm steps are all proved. -/
theorem fixed_dilation_hockey_filter_of_slack_attainment
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E) {γ : ℝ}
    (hγ : 0 ≤ γ) (hV : dilationChannel V = N.toLinearMap)
    (hattain : HockeySlackAttainment γ N M) :
    ∃ W : A →ₗ[ℂ] B ⊗[ℂ] E,
      CPLe (dilationChannel W) ((γ : ℂ) • M.toLinearMap) ∧
      ‖(V - W).toContinuousLinearMap‖ ≤ Real.sqrt (channelHockey γ N M) := by
  obtain ⟨Q, hQ, hdom, htrace⟩ := hattain
  exact fixed_dilation_filter_of_cp_slack V ((γ : ℂ) • M.toLinearMap) Q
    (channelHockey γ N M) (channelHockey_nonneg hγ N M)
    (cp_smul_nonneg ⟨M.toCompletelyPositiveMap, rfl⟩ hγ) hQ
    (by simpa only [hV] using hdom) htrace

end QuantumChannelContinuity
