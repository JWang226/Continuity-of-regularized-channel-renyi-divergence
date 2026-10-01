/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.StabilizedSchatten
import QuantumChannelContinuity.Channels

/-!
# Support-aware divergence form of the Schatten estimate

The component CP bounds imply support inclusion even at singular outputs.
The quasi-entropy is strictly positive there, so the matrix bound can be
converted to the actual extended-real Rényi divergence without an extra
support or positivity hypothesis.
-/

open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy
open scoped TensorProduct ComplexOrder NNReal

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

namespace QuantumChannelContinuity

universe u
variable {A B E R : Type u} [Qudit A] [Qudit B] [Qudit E] [Qudit R]

/-- CP domination of the pieces puts the complete output in the reference
output's support, including for arbitrary entangled inputs. -/
theorem stabilized_channel_dilation_support {ι : Type*} [Fintype ι]
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (lam : ι → ℝ)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (ψ : A ⊗[ℂ] R) :
    LinearMap.ker
      (tensorSuperoperator M.toLinearMap (LinearMap.id : T R R) (outer_product ψ ψ)) ≤
    LinearMap.ker
      (tensorSuperoperator N.toLinearMap (LinearMap.id : T R R) (outer_product ψ ψ)) := by
  let ρ := outer_product ψ ψ
  let σ := tensorSuperoperator M.toLinearMap (LinearMap.id : T R R) ρ
  let C := fun i => vectorCoefficient (stabilizedDilation (R := R) (U i) ψ)
  have hC (i : ι) : coefficientDensity (C i) ≤ lam i • σ := by
    rw [coefficientDensity_vector]
    have h := ((hdom i).tensor_identity_scaled (C := R)
      (dilationChannel_cp (U i))).apply_nonneg (outer_product_self_nonneg ψ)
    rw [← dilationChannel_stabilized] at h
    simpa only [dilationChannel, LinearMap.comp_apply, krausTerm,
      LinearMap.coe_mk, AddHom.coe_mk, comp_outer_product_adjoint,
      LinearMap.smul_apply] using h
  have h := coefficientDensity_sum_support σ C lam hC
  have heq : coefficientDensity (∑ i, C i) =
      tensorSuperoperator N.toLinearMap (LinearMap.id : T R R) ρ := by
    dsimp [C]
    rw [← map_sum, ← LinearMap.sum_apply, ← stabilizedDilation_sum, ← hVU,
      coefficientDensity_vector]
    have hd := congrArg (fun Φ : T (A ⊗[ℂ] R) (B ⊗[ℂ] R) => Φ ρ)
      (dilationChannel_stabilized (R := R) V)
    rw [hV] at hd
    simpa only [dilationChannel, LinearMap.comp_apply, krausTerm, ρ,
      LinearMap.coe_mk, AddHom.coe_mk, comp_outer_product_adjoint] using hd
  rw [heq] at h
  exact h

/-- The public spectral formula for arbitrary real powers on eigenvectors. -/
theorem operator_rpow_apply_eigenvector [Nontrivial B] {X : L B} (hX : 0 ≤ X)
    (t : ℝ) {v : B} {a : ℝ} (hv : X v = (a : ℂ) • v)
    (ha : a ∈ spectrum ℝ X) : CFC.rpow X t v = ((a ^ t : ℝ) : ℂ) • v := by
  have heq : CFC.rpow X t = cfc (fun x : ℝ => x ^ t) X := by
    rw [CFC.rpow_eq_pow]
    exact CFC.rpow_eq_cfc_real (ha := hX)
  rw [heq]
  exact cfc_real_apply_eigenvector
    ((LinearMap.nonneg_iff_isPositive _).1 hX).isSelfAdjoint _ hv ha

/-- Strict positivity of the quasi-entropy on the support region. This
includes singular states and does not assume a positive-definite reference. -/
theorem sandwichedQuasi_pos_of_support [Nontrivial B] {p : ℝ} (hp : 0 < p)
    (ρ σ : L B) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hs : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    0 < (sandwichedQuasi p ρ σ).re := by
  let t := (1 - p) / (2 * p)
  let S := CFC.rpow σ t
  let X := S * ρ * S
  have hS : S.IsPositive := (LinearMap.nonneg_iff_isPositive _).1 CFC.rpow_nonneg
  have hX : 0 ≤ X := conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg
  have hX0 : X ≠ 0 := by
    intro hzero
    apply hρ0
    let hσp := (LinearMap.nonneg_iff_isPositive _).1 hσ
    let b := hσp.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ B) rfl
    let eig := hσp.isSymmetric.eigenvalues (n := Module.finrank ℂ B) rfl
    have heig (i : Fin (Module.finrank ℂ B)) : σ (b i) = (eig i : ℂ) • b i :=
      hσp.isSymmetric.apply_eigenvectorBasis rfl i
    have hρb (i : Fin (Module.finrank ℂ B)) : ρ (b i) = 0 := by
      by_cases hi : eig i = 0
      · exact hs (by rw [LinearMap.mem_ker, heig, hi]; simp)
      · have hi0 : 0 < eig i := lt_of_le_of_ne (hσp.nonneg_eigenvalues rfl i) (Ne.symm hi)
        have hSi : S (b i) = (((eig i) ^ t : ℝ) : ℂ) • b i :=
          operator_rpow_apply_eigenvector hσ t (heig i)
            (mem_spectrum_real_of_eigenvector (b.orthonormal.ne_zero i) (heig i))
        have hinner : (inner ℂ (ρ (S (b i))) (S (b i))).re = 0 := by
          rw [← hS.isSymmetric (ρ (S (b i))) (b i)]
          change (inner ℂ (X (b i)) (b i)).re = 0
          rw [hzero]
          simp
        have hρS : ρ (S (b i)) = 0 :=
          nonneg_apply_eq_zero_of_inner_self_eq_zero hρ hinner
        rw [hSi, map_smul] at hρS
        exact (smul_eq_zero.mp hρS).resolve_left
          (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hi0 t).ne')
    apply b.toBasis.ext
    intro i
    exact hρb i
  have hpow : CFC.rpow X p ≠ 0 := by
    intro hzero
    have h := CFC.rpow_rpow_of_exponent_nonneg X p (1 / p) hp.le
      (by positivity) hX
    rw [mul_one_div_cancel hp.ne', CFC.rpow_one X hX] at h
    change CFC.rpow (CFC.rpow X p) (1 / p) = X at h
    rw [hzero, CFC.zero_rpow (one_div_ne_zero hp.ne')] at h
    exact hX0 h.symm
  exact trace_re_pos_of_ne_zero CFC.rpow_nonneg hpow

/-- Converting a quasi-entropy root bound to the support-aware divergence in
bits; positivity is proved from normalization and support inclusion. -/
theorem stateRenyi_le_of_quasi_root [Nontrivial B] {p z : ℝ} (hp : 1 < p)
    (ρ σ : DensityState B) (hs : suppLE ρ.op σ.op)
    (hz : (sandwichedQuasi p ρ.op σ.op).re ^ (1 / (2 * p)) ≤ z) :
    stateRenyi p ρ σ ≤ ((2 * p / (p - 1)) * Real.logb 2 z : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ.op σ.op ρ.nonneg σ.nonneg hs ρ.op_ne_zero
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Real.rpow_pos_of_pos hQ (1 / (2 * p))) hz
  rw [Real.logb_rpow_eq_mul_logb_of_pos hQ] at hlog
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2 * p / (p - 1) by positivity)
  rw [stateRenyi_eq_formula hp ρ σ hs]
  apply EReal.coe_le_coe_iff.2
  convert h using 1
  field_simp

/-- Exact exponential form of the actual normalized Rényi divergence. -/
theorem rpow_stateRenyi_eq_quasi_root [Nontrivial B] {p : ℝ} (hp : 1 < p)
    (ρ σ : DensityState B) (hs : suppLE ρ.op σ.op) :
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (stateRenyi p ρ σ).toReal) =
      (sandwichedQuasi p ρ.op σ.op).re ^ (1 / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hQ := sandwichedQuasi_pos_of_support hp0 ρ.op σ.op ρ.nonneg σ.nonneg hs ρ.op_ne_zero
  rw [stateRenyi_eq_formula hp ρ σ hs, EReal.toReal_coe]
  have heq : (p - 1) / (2 * p) * (1 / (p - 1) *
      Real.logb 2 (sandwichedQuasi p ρ.op σ.op).re) =
      Real.logb 2 (sandwichedQuasi p ρ.op σ.op).re * (1 / (2 * p)) := by
    field_simp
  rw [heq, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hQ]

/-- The concrete stabilized channel divergence obeys the Stinespring/Schatten
logarithmic upper bound. The supremum includes every entangled pure input. -/
theorem channelRenyi_dilation_bound [Nontrivial A] [Nontrivial B]
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    channelRenyi p N M ≤ ENNReal.ofReal ((2 * p / (p - 1)) *
      Real.logb 2 (∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)))) := by
  apply iSup_le
  intro ψ
  have hs : suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op :=
    stabilized_channel_dilation_support N M V hV U hVU lam hdom ψ.vector
  have hQ := amplify_channel_dilation_schatten_bound hp hp2 N M V hV U hVU
    b lam hb hlam hdom hnorm ψ.vector ψ.norm_one
  exact EReal.toENNReal_le_toENNReal
    (stateRenyi_le_of_quasi_root hp (amplifiedOutput N ψ.density)
      (amplifiedOutput M ψ.density) hs hQ)

/-- The one-shot estimate in the manuscript's exponential notation, for the
actual stabilized channel divergence. Its finiteness is a conclusion. -/
theorem channelRenyi_dilation_exponential_bound [Nontrivial A] [Nontrivial B]
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (N M : CPTP A B) (V : A →ₗ[ℂ] B ⊗[ℂ] E)
    (hV : dilationChannel V = N.toLinearMap)
    (U : ι → A →ₗ[ℂ] B ⊗[ℂ] E) (hVU : V = ∑ i, U i)
    (b lam : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hlam : ∀ i, 0 ≤ lam i)
    (hdom : ∀ i, CPLe (dilationChannel (U i)) (lam i • M.toLinearMap))
    (hnorm : ∀ i, ‖(U i).toContinuousLinearMap‖ ≤ b i) :
    channelRenyi p N M ≠ ⊤ ∧
    (2 : ℝ) ^ ((p - 1) / (2 * p) * (channelRenyi p N M).toReal) ≤
      ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p)) := by
  classical
  let S := ∑ i, b i ^ (1 / p) * lam i ^ ((p - 1) / (2 * p))
  let L := (2 * p / (p - 1)) * Real.logb 2 S
  let ψ : PureInput (A ⊗[ℂ] A) := Classical.choice inferInstance
  have hs : suppLE (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op :=
    stabilized_channel_dilation_support N M V hV U hVU lam hdom ψ.vector
  have hQ := amplify_channel_dilation_schatten_bound hp hp2 N M V hV U hVU
    b lam hb hlam hdom hnorm ψ.vector ψ.norm_one
  have hp0 : 0 < p := by linarith
  have hpm : 0 < p - 1 := by linarith
  have hQpos := sandwichedQuasi_pos_of_support hp0
    (amplifiedOutput N ψ.density).op (amplifiedOutput M ψ.density).op
    (amplifiedOutput N ψ.density).nonneg (amplifiedOutput M ψ.density).nonneg
    hs (amplifiedOutput N ψ.density).op_ne_zero
  have hS : 0 < S := (Real.rpow_pos_of_pos hQpos (1 / (2 * p))).trans_le hQ
  have hstate := stateRenyi_le_of_quasi_root hp (amplifiedOutput N ψ.density)
    (amplifiedOutput M ψ.density) hs hQ
  have hL : 0 ≤ L := by
    have h : (0 : EReal) ≤ (L : EReal) :=
      (stateRenyi_nonneg (by linarith) hp.ne' _ _).trans hstate
    exact_mod_cast h
  have hD := channelRenyi_dilation_bound hp hp2 N M V hV U hVU b lam hb hlam hdom hnorm
  change channelRenyi p N M ≤ ENNReal.ofReal L at hD
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
  rw [ENNReal.toReal_ofReal hL] at hreal
  calc
    _ ≤ (2 : ℝ) ^ ((p - 1) / (2 * p) * L) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hreal (by positivity))
    _ = (2 : ℝ) ^ Real.logb 2 S := by
      congr 1
      dsimp [L]
      field_simp
    _ = S := Real.rpow_logb (by norm_num) (by norm_num) hS

end QuantumChannelContinuity
