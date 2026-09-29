import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic

/-!
# Block suprema on multiples

The regularization identity on positive multiples follows directly from
superadditivity. All operations retain infinite values.
-/

open scoped ENNReal
namespace QuantumChannelContinuity

/-- Repeating a block gives the natural-multiple bound for an extended-real
superadditive sequence, including zero and infinite values. -/
theorem ennreal_nat_mul_le_apply_mul (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) (n k : ℕ) :
    (n : ℝ≥0∞) * f k ≤ f (n * k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ((n + 1 : ℕ) : ℝ≥0∞) * f k = (n : ℝ≥0∞) * f k + f k := by
        simp [add_mul]
      _ ≤ f (n * k) + f k := add_le_add ih le_rfl
      _ ≤ f (n * k + k) := hf _ _
      _ = f ((n + 1) * k) := by rw [Nat.add_mul, one_mul]

/-- Exact positive-block scaling of a regularized supremum, using only the
block repetition inequality. No limit or finiteness premise is needed. -/
theorem ennreal_iSup_div_multiples_of_repeat (f : ℕ → ℝ≥0∞)
    (hf : ∀ n k : ℕ, (n : ℝ≥0∞) * f k ≤ f (n * k))
    {n : ℕ} (hn : 0 < n) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), f (n * k) / (k : ℝ≥0∞)) =
      (n : ℝ≥0∞) * (⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞)) := by
  apply le_antisymm
  · refine iSup_le fun k => iSup_le fun hk => ?_
    have hnk : 0 < n * k := Nat.mul_pos hn hk
    have hbound : f (n * k) / ((n * k : ℕ) : ℝ≥0∞) ≤
        ⨆ j : ℕ, ⨆ (_ : 0 < j), f j / (j : ℝ≥0∞) :=
      le_iSup_of_le (n * k) (le_iSup_of_le hnk le_rfl)
    have hraw := (ENNReal.div_le_iff (by exact_mod_cast hnk.ne')
      (ENNReal.natCast_ne_top (n * k))).mp hbound
    apply (ENNReal.div_le_iff (by exact_mod_cast hk.ne') (by simp)).mpr
    simpa only [Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hraw
  · simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun k => iSup_le fun hk => ?_
    apply le_iSup_of_le k
    apply le_iSup_of_le hk
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_right' (hf n k) (k : ℝ≥0∞)⁻¹

/-- A superadditive sequence has the exact regularization scaling on all
positive block multiples. -/
theorem ennreal_iSup_div_multiples (f : ℕ → ℝ≥0∞)
    (hf : ∀ m n, f m + f n ≤ f (m + n)) {n : ℕ} (hn : 0 < n) :
    (⨆ k : ℕ, ⨆ (_ : 0 < k), f (n * k) / (k : ℝ≥0∞)) =
      (n : ℝ≥0∞) * (⨆ k : ℕ, ⨆ (_ : 0 < k), f k / (k : ℝ≥0∞)) :=
  ennreal_iSup_div_multiples_of_repeat f (ennreal_nat_mul_le_apply_mul f hf) hn

end QuantumChannelContinuity
