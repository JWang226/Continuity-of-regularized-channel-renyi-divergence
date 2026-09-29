import QuantumChannelContinuity.ThreePieceFilter
import QuantumChannelContinuity.TensorWords

/-!
# Three-piece filter–Schatten estimate on actual entangled channel outputs

This composes the constructed operators with the proved stabilized Schatten
inequality. The sole unproved filtering premise is exact CP-slack attainment.
Tensor words and the block-supremum bound are proved in `TensorWords`.
The further block-power scaling needed to instantiate the main threshold
argument remains separate.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped ComplexOrder TensorProduct

namespace QuantumChannelContinuity

universe u
variable {A B E : Type u} [Qudit A] [Qudit B] [Qudit E]
  [Nontrivial A] [Nontrivial B]

/-- The manuscript's three-term quantum estimate for every actual stabilized
pure input, with no assumed Schatten inequality or assumed filter operators. -/
theorem hockey_three_piece_schatten (N M : CPTP A B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (γlow γhigh C : ℝ)
    (hγlow : 0 ≤ γlow) (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (ψ : PureInput (A ⊗[ℂ] A)) :
    (sandwichedQuasi p (amplifiedOutput N ψ.density).op
      (amplifiedOutput M ψ.density).op).re ^ (1 / (2 * p)) ≤
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
    simpa [U, Fin.sum_univ_succ, add_assoc] using hsum.symm
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
  have h := amplify_channel_dilation_schatten_bound hp hp2 N M V hV U hsumU
    b lam hb hlam hdom hnorm ψ.vector ψ.norm_one
  simpa [amplifiedOutput, PureInput.density, b, lam, Fin.sum_univ_succ, add_assoc] using h

/-- The corresponding bound on the actual stabilized channel divergence,
including the optimization over all entangled inputs and support handling. -/
theorem hockey_three_piece_channelRenyi (N M : CPTP A B)
    (V : A →ₗ[ℂ] B ⊗[ℂ] E) (γlow γhigh C : ℝ)
    (hγlow : 0 ≤ γlow) (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    channelRenyi p N M ≤ ENNReal.ofReal ((2 * p / (p - 1)) * Real.logb 2 (
      (1 + Real.sqrt (channelHockey γlow N M)) ^ (1 / p) * γlow ^ ((p - 1) / (2 * p)) +
      (Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M)) ^ (1 / p) *
        (4 * γhigh) ^ ((p - 1) / (2 * p)) +
      Real.sqrt (channelHockey γhigh N M) ^ (1 / p) * (4 * C) ^ ((p - 1) / (2 * p)))) := by
  apply iSup_le
  intro ψ
  have hdom : ∀ _ : Unit, CPLe (dilationChannel V) (C • M.toLinearMap) := by
    intro _
    rw [hV]
    have hsmul : (C : ℂ) • M.toLinearMap = C • M.toLinearMap :=
      IsScalarTower.algebraMap_smul ℂ C M.toLinearMap
    simpa only [hsmul] using hcap
  have hs := stabilized_channel_dilation_support N M V hV
    (fun _ : Unit => V) (by simp) (fun _ : Unit => C) hdom ψ.vector
  have hQ := hockey_three_piece_schatten N M V γlow γhigh C hγlow hγle hγC
    hV hcap hlow hhigh hp hp2 ψ
  exact EReal.toENNReal_le_toENNReal
    (stateRenyi_le_of_quasi_root hp (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) hs hQ)

/-- The three-piece bound for the actual regularized block supremum. Tensor
words, their common dilation, their CP/norm product bounds and optimization
are all proved. The exact low/high slack optima and channel domination
remain explicit premises. -/
theorem hockey_three_piece_regularizedRenyi
    {A B E : Type} [Qudit A] [Qudit B] [Qudit E]
    [Nontrivial A] [Nontrivial B] [Nontrivial E]
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E) (γlow γhigh C : ℝ)
    (hγlow : 0 ≤ γlow) (hγle : γlow ≤ γhigh) (hγC : γhigh ≤ C)
    (hV : dilationChannel V = N.toLinearMap)
    (hcap : CPLe N.toLinearMap ((C : ℂ) • M.toLinearMap))
    (hlow : HockeySlackAttainment γlow N M)
    (hhigh : HockeySlackAttainment γhigh N M)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    regularizedRenyi p N M ≤ ENNReal.ofReal ((2 * p / (p - 1)) * Real.logb 2 (
      (1 + Real.sqrt (channelHockey γlow N M)) ^ (1 / p) * γlow ^ ((p - 1) / (2 * p)) +
      (Real.sqrt (channelHockey γlow N M) + Real.sqrt (channelHockey γhigh N M)) ^ (1 / p) *
        (4 * γhigh) ^ ((p - 1) / (2 * p)) +
      Real.sqrt (channelHockey γhigh N M) ^ (1 / p) * (4 * C) ^ ((p - 1) / (2 * p)))) := by
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
    simpa [U, Fin.sum_univ_succ, add_assoc] using hsum.symm
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
  have h := regularizedRenyi_dilation_bound hp hp2 N M V hV U hsumU
    b lam hb hlam hdom hnorm
  simpa [b, lam, Fin.sum_univ_succ, add_assoc] using h

end QuantumChannelContinuity
