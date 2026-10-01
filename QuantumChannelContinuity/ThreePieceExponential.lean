/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.ThreePieceSchatten
import QuantumChannelContinuity.RegularizedExponential

/-!
# The three-piece regularized estimate in exponential form

The low and high filters, all tensor words, reference amplification, support
conditions, and passage to the block supremum are proved. Exact CP-slack
attainment and the channel domination cap remain the explicit input premises.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

/-- The manuscript's three-term exponential bound on the actual regularized
channel Rényi divergence, with finiteness proved at the same time. -/
theorem hockey_three_piece_regularized_exponential
    {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
    [Nontrivial A] [Nontrivial B] [Nontrivial E]
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E) (γlow γhigh C : ℝ)
    (hγlow : 0 ≤ γlow) (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    regularizedRenyi p N M ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (regularizedRenyi p N M).toReal) ≤
      (1 + Real.sqrt (channelHockey γlow N M)) ^ (1 / p) * γlow ^ ((p - 1) / (2 * p)) +
      (Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M)) ^ (1 / p) *
        (4 * γhigh) ^ ((p - 1) / (2 * p)) +
      Real.sqrt (channelHockey γhigh N M) ^ (1 / p) * (4 * C) ^ ((p - 1) / (2 * p)) := by
  classical
  obtain ⟨X, W, hsum, hX, hWX, hVW, hXcp, hWXcp, hVWcp⟩ :=
    hockey_three_piece_decomposition N M V γlow γhigh C hγlow hγle hγC
      hV hcap hlow hhigh
  let U : Fin 3 → A →ₗ[ℂ] B ⊗[ℂ] E := ![X, W - X, V - W]
  let b : Fin 3 → ℝ := ![1 + Real.sqrt (channelHockey γlow N M),
    Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M),
    Real.sqrt (channelHockey γhigh N M)]
  let lam : Fin 3 → ℝ := ![γlow, 4 * γhigh, 4 * C]
  have hsumU : V = ∑ i, U i := by
    simp [U, Fin.sum_univ_succ]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> simp [b] <;> positivity
  have hlam : ∀ i, 0 ≤ lam i := by
    intro i
    fin_cases i <;> simp [lam]
    · exact hγlow
    · exact hγlow.trans hγle
    · exact (hγlow.trans hγle).trans hγC
  have hsmul (c : ℝ) : (c : ℂ) • M.toLinearMap = c • M.toLinearMap :=
    IsScalarTower.algebraMap_smul ℂ c M.toLinearMap
  rw [hsmul] at hXcp hWXcp hVWcp
  have hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap) := by
    intro i
    fin_cases i
    · simpa [U, lam] using hXcp
    · simpa [U, lam] using hWXcp
    · simpa [U, lam] using hVWcp
  have hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i := by
    intro i
    fin_cases i
    · exact hX
    · exact hWX
    · exact hVW
  have h := regularizedRenyi_dilation_exponential_bound hp hp2 N M V hV U hsumU
    b lam hb hlam hdom hnorm
  simpa [b, lam, Fin.sum_univ_succ, add_assoc] using h

end QuantumChannelContinuity
