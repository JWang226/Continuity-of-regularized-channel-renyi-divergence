import QuantumChannelContinuity.TensorChannels
import QuantumChannelContinuity.ChannelTesting

/-!
# Concrete tensor powers and block-supremum divergences

The regularized quantities are defined as suprema over positive block lengths.
Their identification with limits via superadditivity/Fekete is a separate
obligation, not asserted by these definitions.
-/

open QuantumState QuantumChannel
open scoped ComplexOrder TensorProduct ENNReal

namespace QuantumChannelContinuity

/-- A bundled nonzero finite-dimensional Hilbert space for dependent tensor
power recursion. -/
structure HilbertBlock where
  Space : Type
  qudit : Qudit Space
  nontrivial : Nontrivial Space

attribute [instance] HilbertBlock.qudit HilbertBlock.nontrivial

/-- A canonical tensor power, with the one-dimensional space as unit. -/
noncomputable def tensorPowerSpace (H : Type) [Qudit H] [Nontrivial H] : ℕ → HilbertBlock
  | 0 => ⟨EuclideanSpace ℂ (Fin 1), inferInstance, inferInstance⟩
  | n + 1 => ⟨H ⊗[ℂ] (tensorPowerSpace H n).Space, inferInstance, inferInstance⟩

abbrev TensorPower (H : Type) [Qudit H] [Nontrivial H] (n : ℕ) :=
  (tensorPowerSpace H n).Space

/-- The identity CPTP channel. -/
noncomputable def identityChannel (H : Type) [Qudit H] : CPTP H H where
  toFun := id
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_cstarMatrix_nonneg' k X hX := by simpa only [CStarMatrix.map_id] using hX
  trace_map _ := rfl

variable {H K : Type} [Qudit H] [Qudit K] [Nontrivial H] [Nontrivial K]

/-- Actual tensor powers of the supplied CPTP map. -/
noncomputable def channelPower (N : CPTP H K) :
    (n : ℕ) → CPTP (TensorPower H n) (TensorPower K n)
  | 0 => identityChannel _
  | n + 1 => tensorChannel N (channelPower N n)

/-- Stabilized Rényi divergence of the actual `n`-fold tensor powers. -/
noncomputable def blockRenyi (α : ℝ) (N M : CPTP H K) (n : ℕ) : ℝ≥0∞ :=
  channelRenyi α (channelPower N n) (channelPower M n)

/-- Stabilized relative entropy of the actual `n`-fold tensor powers. -/
noncomputable def blockRelative (N M : CPTP H K) (n : ℕ) : ℝ≥0∞ :=
  channelRelative (channelPower N n) (channelPower M n)

/-- The block-supremum definition of regularized channel Rényi divergence. -/
noncomputable def regularizedRenyi (α : ℝ) (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRenyi α N M n / (n : ℝ≥0∞)

/-- The block-supremum definition of regularized channel relative entropy. -/
noncomputable def regularizedRelative (N M : CPTP H K) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ (_ : 0 < n), blockRelative N M n / (n : ℝ≥0∞)

/-- Concrete block testing quantity at the manuscript's threshold. -/
noncomputable def blockTesting (N M : CPTP H K) (n : ℕ) (r : ℝ) : ℝ :=
  channelHockey ((2 : ℝ) ^ ((n : ℝ) * r)) (channelPower N n) (channelPower M n)

theorem blockRenyi_le_regularized (α : ℝ) (N M : CPTP H K) {n : ℕ} (hn : 0 < n) :
    blockRenyi α N M n ≤ regularizedRenyi α N M * (n : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mp
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

theorem blockRelative_le_regularized (N M : CPTP H K) {n : ℕ} (hn : 0 < n) :
    blockRelative N M n ≤ regularizedRelative N M * (n : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (by exact_mod_cast hn.ne') (by simp)).mp
  exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

theorem blockTesting_nonneg (N M : CPTP H K) (n : ℕ) (r : ℝ) :
    0 ≤ blockTesting N M n r :=
  channelHockey_nonneg (Real.rpow_nonneg (by norm_num) _) _ _

theorem blockTesting_le_one (N M : CPTP H K) (n : ℕ) (r : ℝ) :
    blockTesting N M n r ≤ 1 :=
  channelHockey_le_one (Real.rpow_nonneg (by norm_num) _) _ _

/-- The concrete weak bound uses the actual finite regularized divergence;
all quantum testing steps and the block supremum bound are proved. -/
theorem regularized_weak_testing (N M : CPTP H K)
    (hfin : regularizedRelative N M ≠ ⊤) {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    blockTesting N M n r ≤ (regularizedRelative N M).toReal / r +
      1 / ((n : ℝ) * r) := by
  apply block_channelHockey_relative_bound _ _ hn hr ENNReal.toReal_nonneg
  change blockRelative N M n ≤ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_toReal hfin]
  simpa [mul_comm] using blockRelative_le_regularized N M hn

/-- The concrete exponential bound, expressed in terms of the actual
finite block-supremum Rényi divergence. -/
theorem regularized_renyi_testing (N M : CPTP H K) {α : ℝ} (hα : 1 < α)
    (hfin : regularizedRenyi α N M ≠ ⊤) {n : ℕ} (hn : 0 < n) (ell : ℝ) :
    blockTesting N M n ell ≤
      (2 : ℝ) ^ (-(n : ℝ) * (α - 1) * (ell - (regularizedRenyi α N M).toReal)) := by
  apply block_channelHockey_renyi_bound _ _ n hα ENNReal.toReal_nonneg
  change blockRenyi α N M n ≤ _
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_toReal hfin]
  simpa [mul_comm] using blockRenyi_le_regularized α N M hn

end QuantumChannelContinuity
