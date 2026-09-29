import QuantumChannelContinuity.StateDominationBounds
import QuantumChannelContinuity.ChoiSupport
import QuantumChannelContinuity.QuantumMain

/-!
# Finite channel caps and regularized finiteness

A concrete CP domination constant yields uniform normalized-block bounds for
both divergences. The cap and all finiteness fields are consequences, not
extra quantum hypotheses.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder TensorProduct ENNReal Topology
namespace QuantumChannelContinuity

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [Qudit A] [Qudit B] [Nontrivial A] [Nontrivial B]

/-- Trace preservation forces every channel domination constant to be at least one. -/
theorem cp_domination_constant_ge_one (N M : CPTP A B) {c : ℝ}
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) : 1 ≤ c := by
  let ρ := DensityState.maximallyMixed A
  have h := hdom.apply_nonneg ρ.nonneg
  have htr := trace_mul_re_mono h (1 : L B)
    ((LinearMap.nonneg_iff_isPositive _).mp zero_le_one)
  have hN : Tr (N.toLinearMap ρ.op) = 1 := (N.trace_map ρ.op).symm.trans ρ.trace_one
  have hM : Tr (M.toLinearMap ρ.op) = 1 := (M.trace_map ρ.op).symm.trans ρ.trace_one
  simpa only [mul_one, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
    Complex.real_smul, hN, hM, Complex.one_re, mul_one] using htr

/-- CP domination holds on every stabilized output with the same constant. -/
theorem cp_domination_amplifiedOutput (N M : CPTP A B) {c : ℝ}
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap))
    (ρ : DensityState (A ⊗[ℂ] A)) :
    (amplifiedOutput N ρ).op ≤ c • (amplifiedOutput M ρ).op := by
  exact (hdom.tensor_identity_scaled (C := A) ⟨N.toCompletelyPositiveMap, rfl⟩).apply_nonneg
    ρ.nonneg

/-- Tensor powers preserve the finite scalar CP bound multiplicatively. -/
theorem channelPower_cp_domination (N M : CPTP A B) {c : ℝ} (hc : 0 ≤ c)
    (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) (n : ℕ) :
    CPLe (channelPower N n).toLinearMap ((c ^ n) • (channelPower M n).toLinearMap) := by
  induction n with
  | zero =>
    change CPLe (LinearMap.id : T (TensorPower A 0) (TensorPower B 0)) (c ^ 0 • LinearMap.id)
    simp only [pow_zero, one_smul, CPLe, sub_self]
    simpa using cp_smul (cp_identity (C := TensorPower A 0)) (c := 0) le_rfl
  | succ n ih =>
    have h := hdom.tensor_scaled ih ⟨N.toCompletelyPositiveMap, rfl⟩
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩ (pow_nonneg hc n)
    simpa only [channelPower, tensorChannel, pow_succ, mul_comm] using h

/-- An explicit finite bound for every stabilized Rényi divergence above one. -/
theorem channelRenyi_le_of_cp_domination (N M : CPTP A B) {p c : ℝ}
    (hp : 1 < p) (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    channelRenyi p N M ≤ ENNReal.ofReal (p / (p - 1) * Real.logb 2 c) := by
  apply iSup_le
  intro ψ
  exact EReal.toENNReal_le_toENNReal
    (stateRenyi_le_coarse_log_of_le hp hc (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) (cp_domination_amplifiedOutput N M hdom ψ.density))

/-- The normalized block-supremum Rényi divergence is finite at every `p>1`. -/
theorem regularizedRenyi_le_of_cp_domination (N M : CPTP A B) {p c : ℝ}
    (hp : 1 < p) (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRenyi p N M ≤ ENNReal.ofReal (p / (p - 1) * Real.logb 2 c) := by
  refine iSup_le fun n => iSup_le fun hn => ?_
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mpr
  have hb := channelRenyi_le_of_cp_domination (channelPower N n) (channelPower M n)
    hp (pow_pos hc n) (channelPower_cp_domination N M hc.le hdom n)
  rw [Real.logb_pow] at hb
  have heq : p / (p - 1) * ((n : ℝ) * Real.logb 2 c) =
      (p / (p - 1) * Real.logb 2 c) * (n : ℝ) := by ring
  rw [heq, ENNReal.ofReal_mul' (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hb
  exact hb

/-- An explicit finite Umegaki bound on the stabilized channel supremum. -/
theorem channelRelative_le_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 1 ≤ c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    channelRelative N M ≤ ENNReal.ofReal (Real.logb 2 c) := by
  apply iSup_le
  intro ψ
  exact EReal.toENNReal_le_toENNReal
    (stateRelative_le_log_of_le hc (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) (cp_domination_amplifiedOutput N M hdom ψ.density))

/-- Uniform normalized-block Umegaki bound, including every entangled input. -/
theorem regularizedRelative_le_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 1 ≤ c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRelative N M ≤ ENNReal.ofReal (Real.logb 2 c) := by
  refine iSup_le fun n => iSup_le fun hn => ?_
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mpr
  have hb := channelRelative_le_of_cp_domination (channelPower N n) (channelPower M n)
    (one_le_pow₀ hc) (channelPower_cp_domination N M (zero_le_one.trans hc) hdom n)
  rw [Real.logb_pow, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast] at hb
  simpa only [mul_comm] using hb

/-- All finiteness fields of the continuity interface follow from one finite CP bound. -/
theorem regularized_finite_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    regularizedRelative N M ≠ ⊤ ∧ ∀ p, 1 < p → regularizedRenyi p N M ≠ ⊤ := by
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularizedRelative_le_of_cp_domination N M (cp_domination_constant_ge_one N M hdom) hdom), ?_⟩
  intro p hp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (regularizedRenyi_le_of_cp_domination N M hp hc hdom)

/-- A completely explicit cap for the threshold and all block domination bounds. -/
theorem finite_cap_of_cp_domination (N M : CPTP A B) {c : ℝ}
    (hc : 0 < c) (hdom : CPLe N.toLinearMap (c • M.toLinearMap)) :
    ∃ cap : ℝ, rightThreshold N M ≤ cap ∧
      ∀ n : ℕ, CPLe (channelPower N n).toLinearMap
        (((2 : ℝ) ^ ((n : ℝ) * (cap + 1))) • (channelPower M n).toLinearMap) := by
  have hc1 := cp_domination_constant_ge_one N M hdom
  have hlog : 0 ≤ Real.logb 2 c := Real.logb_nonneg (by norm_num) hc1
  refine ⟨2 * Real.logb 2 c, ?_, ?_⟩
  · have hth : rightThreshold N M ≤ (regularizedRenyi 2 N M).toReal := by
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨p, hp, rfl⟩; exact ENNReal.toReal_nonneg⟩
      · exact ⟨2, by norm_num, rfl⟩
    have hb := regularizedRenyi_le_of_cp_domination N M (p := 2) (by norm_num) hc hdom
    norm_num only [sub_self, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num, div_one] at hb
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal (by positivity)] at hr
    exact hth.trans hr
  · intro n
    have hb := channelPower_cp_domination N M hc.le hdom n
    have hscale : c ^ n ≤ (2 : ℝ) ^ ((n : ℝ) * (2 * Real.logb 2 c + 1)) := by
      calc
        c ^ n = (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 c) := by
          rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_logb (by norm_num) (by norm_num) hc, Real.rpow_natCast]
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n))
    have hm := cp_smul_mono (channelPower M n).toLinearMap
      ⟨(channelPower M n).toCompletelyPositiveMap, rfl⟩ hscale
    have heq (x : ℝ) : (x : ℂ) • (channelPower M n).toLinearMap =
        x • (channelPower M n).toLinearMap :=
      IsScalarTower.algebraMap_smul ℂ x (channelPower M n).toLinearMap
    simpa only [heq] using hb.trans (by simpa only [heq] using hm)

end QuantumChannelContinuity
