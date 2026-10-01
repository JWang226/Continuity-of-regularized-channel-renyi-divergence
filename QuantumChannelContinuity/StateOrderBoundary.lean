/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/

import QuantumChannelContinuity.StateOrderApprox

/-! # Extending order inequalities from faithful to arbitrary density states -/
open QuantumState QuantumChannel SandwichedRenyiRelativeEntropy Filter Set
open scoped ComplexOrder Topology
namespace QuantumChannelContinuity
namespace OrderBoundary
universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

abbrev ApproxParameter := {l : ℝ // 0 < l ∧ l ≤ 1}
noncomputable def approxFilter : Filter ApproxParameter :=
  Filter.comap Subtype.val (𝓝[>] (0 : ℝ))

instance approxFilter_neBot : approxFilter.NeBot := by
  refine Filter.comap_neBot fun t ht => ?_
  obtain ⟨U,hU,hU0,hsub⟩ := mem_nhdsWithin.mp ht
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hU0)
  have hx : 0 < min (δ / 2) 1 := lt_min (by positivity) one_pos
  refine ⟨⟨min (δ / 2) 1,hx,min_le_right _ _⟩,hsub ⟨hball ?_,hx⟩⟩
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hx]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

noncomputable def identity (H : Type u) [Qudit H] : CPTP H H where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_cstarMatrix_nonneg' k X hX := by simpa only [CStarMatrix.map_id] using hX
  trace_map _ := rfl

noncomputable def approxChannel (H : Type u) [Qudit H] [Nontrivial H]
    (l : ApproxParameter) : CPTP H H :=
  faithfulApprox (identity H) l.val l.property.1.le l.property.2

noncomputable def approx (ρ : DensityState H) (l : ApproxParameter) : DensityState H :=
  ρ.map (approxChannel H l)

theorem approx_pd (ρ : DensityState H) (l : ApproxParameter) :
    (approx ρ l).op ∈ pdSetLM :=
  faithfulApprox_pdSetLM (identity H) l.property.1 l.property.2 ρ.nonneg ρ.op_ne_zero

theorem approx_tendsto (ρ : DensityState H) :
    Tendsto (fun l => (approx ρ l).op) approxFilter (𝓝 ρ.op) :=
  faithfulApprox_tendsto (identity H) ρ.op

theorem stateRenyi_eq_coe_pd {p : ℝ} (hp : 0 < p)
    (ρ σ : DensityState H) (hρ : ρ.op ∈ pdSetLM) (hσ : σ.op ∈ pdSetLM) :
    stateRenyi p ρ σ = ((sandwichedRenyiDiv p ρ.op σ.op / Real.log 2 : ℝ) : EReal) := by
  have hs := suppLE_of_pdSetLM_right ρ.op hσ
  have hQ := sandwichedQuasi_re_ne_zero_of_pdSetLM hp hρ hσ
  simp only [stateRenyi,sandwichedRenyiDivNN,hs,not_true_eq_false,and_false,hQ,
    or_self,↓reduceIte,toBits_coe]

theorem stateRenyi_approx_tendsto_gt {p : ℝ} (hp : 1 < p)
    (ρ σ : DensityState H) (hs : suppLE ρ.op σ.op) :
    Tendsto (fun l => stateRenyi p (approx ρ l) (approx σ l)) approxFilter
      (𝓝 (stateRenyi p ρ σ)) := by
  have hd := sandwichedRenyiDiv_tendsto_faithful (identity H) hp
    ρ.nonneg σ.nonneg σ.op_ne_zero ρ.op_ne_zero hs
  have hb := (continuous_coe_real_ereal.tendsto _).comp (hd.div_const (Real.log 2))
  have htarget : stateRenyi p ρ σ =
      ((sandwichedRenyiDiv p ρ.op σ.op / Real.log 2 : ℝ) : EReal) := by
    simp only [stateRenyi,sandwichedRenyiDivNN,not_lt.mpr hp.le,false_and,
      hs,not_true_eq_false,and_false,or_self,↓reduceIte,toBits_coe]
  rw [htarget]
  apply hb.congr'
  filter_upwards with l
  exact (stateRenyi_eq_coe_pd (by linarith) _ _ (approx_pd ρ l) (approx_pd σ l)).symm

theorem quasi_approx_tendsto_lt {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (ρ σ : DensityState H) :
    Tendsto (fun l => (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re)
      approxFilter (𝓝 (sandwichedQuasi p ρ.op σ.op).re) := by
  have hpair : Tendsto
      (fun l : ApproxParameter => ((approx ρ l).op,(approx σ l).op)) approxFilter
      (𝓝[({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A})] (ρ.op,σ.op)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨(approx_tendsto ρ).prodMk_nhds (approx_tendsto σ),
      Filter.Eventually.of_forall (fun l => ⟨(approx ρ l).nonneg,(approx σ l).nonneg⟩)⟩
  have hc : Tendsto (fun v : L H × L H => (sandwichedQuasi p v.1 v.2).re)
      (𝓝[({A : L H | 0 ≤ A} ×ˢ {A : L H | 0 ≤ A})] (ρ.op,σ.op))
      (𝓝 (sandwichedQuasi p ρ.op σ.op).re) :=
    sandwichedQuasi_re_continuousOn_nonneg hp hp1 (ρ.op,σ.op) ⟨ρ.nonneg,σ.nonneg⟩
  have hh := hc.comp hpair
  exact hh

theorem stateRenyi_approx_eq {p : ℝ} (hp : 0 < p)
    (ρ σ : DensityState H) (l : ApproxParameter) :
    stateRenyi p (approx ρ l) (approx σ l) =
      ((Real.log (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re *
        ((1 / (p - 1)) / Real.log 2) : ℝ) : EReal) := by
  rw [stateRenyi_eq_coe_pd hp _ _ (approx_pd ρ l) (approx_pd σ l)]
  simp only [sandwichedRenyiDiv,(approx ρ l).trace_one,Complex.one_re,div_one]
  congr 1
  ring

/-- Below one, faithful approximations converge even when the limiting states
are orthogonal: the logarithm then tends to minus infinity and the negative
Rényi coefficient sends it to plus infinity. -/
theorem stateRenyi_approx_tendsto_lt {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ρ σ : DensityState H) :
    Tendsto (fun l => stateRenyi p (approx ρ l) (approx σ l)) approxFilter
      (𝓝 (stateRenyi p ρ σ)) := by
  have hQ := quasi_approx_tendsto_lt hp hp1.le ρ σ
  by_cases hz : (sandwichedQuasi p ρ.op σ.op).re = 0
  · have htarget : stateRenyi p ρ σ = ⊤ := by
      simp [stateRenyi,sandwichedRenyiDivNN,hp1,ρ.op_ne_zero,hz]
    rw [htarget]
    have hQpos (l : ApproxParameter) :
        0 < (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re := by
      exact sandwichedQuasi_pos_of_support hp _ _ (approx ρ l).nonneg (approx σ l).nonneg
        (suppLE_of_pdSetLM_right _ (approx_pd σ l)) (approx ρ l).op_ne_zero
    have hQwithin : Tendsto
        (fun l => (sandwichedQuasi p (approx ρ l).op (approx σ l).op).re)
        approxFilter (𝓝[>] (0 : ℝ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hz] using hQ,
        Filter.Eventually.of_forall hQpos⟩
    have hneg : (1 / (p - 1)) / Real.log 2 < 0 :=
      div_neg_of_neg_of_pos (one_div_neg.mpr (sub_neg.mpr hp1)) log_two_pos
    have htop := ((Real.tendsto_log_nhdsGT_zero.comp hQwithin).atBot_mul_const_of_neg hneg)
    apply (EReal.tendsto_coe_atTop.comp htop).congr'
    filter_upwards with l
    exact (stateRenyi_approx_eq hp ρ σ l).symm
  · have hlog := ((Real.continuousAt_log hz).tendsto.comp hQ).mul_const
      ((1 / (p - 1)) / Real.log 2)
    have htarget : stateRenyi p ρ σ =
        ((Real.log (sandwichedQuasi p ρ.op σ.op).re *
          ((1 / (p - 1)) / Real.log 2) : ℝ) : EReal) := by
      simp only [stateRenyi,sandwichedRenyiDivNN,not_lt.mpr hp1.le,false_and,
        hz,and_false,or_self,↓reduceIte,toBits_coe,sandwichedRenyiDiv,
        ρ.trace_one,Complex.one_re,div_one]
      congr 1
      ring
    rw [htarget]
    apply ((continuous_coe_real_ereal.tendsto _).comp hlog).congr'
    filter_upwards with l
    exact (stateRenyi_approx_eq hp ρ σ l).symm

end OrderBoundary

universe u
variable {H : Type u} [Qudit H] [Nontrivial H]
set_option maxHeartbeats 1000000

/-- A proved transfer principle: faithful order monotonicity above one
extends to all density states, including support mismatch. -/
theorem stateRenyi_le_of_faithful_gt {α β : ℝ} (hα : 1 < α) (hαβ : α ≤ β)
    (hfaithful : ∀ (ρ σ : DensityState H), ρ.op ∈ pdSetLM → σ.op ∈ pdSetLM →
      stateRenyi α ρ σ ≤ stateRenyi β ρ σ) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  by_cases hs : suppLE ρ.op σ.op
  · apply le_of_tendsto (OrderBoundary.stateRenyi_approx_tendsto_gt hα ρ σ hs)
    filter_upwards with l
    exact (hfaithful _ _ (OrderBoundary.approx_pd ρ l) (OrderBoundary.approx_pd σ l)).trans
      (stateRenyi_dataProcessing (OrderBoundary.approxChannel H l)
        (by linarith) (by linarith) ρ σ)
  · rw [stateRenyi_eq_top_of_not_support (hα.trans_le hαβ) ρ σ hs]
    exact le_top

/-- The same transfer below one handles zero overlap by actual extended-real
continuity, so it also permits a target order above one. -/
theorem stateRenyi_le_of_faithful_lt {α β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hβ : (1 : ℝ) / 2 ≤ β) (hβ1 : β ≠ 1)
    (hfaithful : ∀ (ρ σ : DensityState H), ρ.op ∈ pdSetLM → σ.op ∈ pdSetLM →
      stateRenyi α ρ σ ≤ stateRenyi β ρ σ) (ρ σ : DensityState H) :
    stateRenyi α ρ σ ≤ stateRenyi β ρ σ := by
  apply le_of_tendsto (OrderBoundary.stateRenyi_approx_tendsto_lt hα hα1 ρ σ)
  filter_upwards with l
  exact (hfaithful _ _ (OrderBoundary.approx_pd ρ l) (OrderBoundary.approx_pd σ l)).trans
    (stateRenyi_dataProcessing (OrderBoundary.approxChannel H l) hβ hβ1 ρ σ)

end QuantumChannelContinuity
