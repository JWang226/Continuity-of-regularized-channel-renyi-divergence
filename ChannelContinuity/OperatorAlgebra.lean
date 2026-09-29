import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-!
# Concrete algebraic ingredients of the channel-continuity proof

These results concern actual rectangular complex matrices.  They verify the
parallelogram identity underlying the CP estimate for differences of dilation
operators, its positivity consequence, and the tensor-word scalar sum.

They do not define partial trace or completely positive maps; accordingly the
positivity consequence is stated as positivity of the matrix difference.
-/

open scoped BigOperators Matrix ComplexOrder

namespace ChannelContinuity

section Matrices

variable {a b : Type*} [Fintype a]

/-- The matrix sandwich associated with a rectangular operator. -/
noncomputable def sandwich (U : Matrix b a ℂ) (ρ : Matrix a a ℂ) : Matrix b b ℂ :=
  U * ρ * Uᴴ

/-- The exact identity behind `Φ_(U-W) ≤ 2 Φ_U + 2 Φ_W`.
No positivity hypothesis is needed for this algebraic identity. -/
theorem sandwich_parallelogram (U W : Matrix b a ℂ) (ρ : Matrix a a ℂ) :
    (2 : ℂ) • sandwich U ρ + (2 : ℂ) • sandwich W ρ -
      sandwich (U - W) ρ = sandwich (U + W) ρ := by
  simp only [sandwich, two_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub]
  abel

variable [Fintype b]

/-- Sandwiching a positive semidefinite matrix preserves positivity. -/
theorem sandwich_posSemidef (U : Matrix b a ℂ) {ρ : Matrix a a ℂ}
    (hρ : ρ.PosSemidef) : (sandwich U ρ).PosSemidef :=
  hρ.mul_mul_conjTranspose_same U

/-- Loewner domination for the difference of two rectangular operators,
expressed by positive semidefiniteness of the upper bound minus the lower bound.
Applying partial trace to this identity is the remaining channel-level step. -/
theorem sandwich_difference_domination (U W : Matrix b a ℂ) {ρ : Matrix a a ℂ}
    (hρ : ρ.PosSemidef) :
    ((2 : ℂ) • sandwich U ρ + (2 : ℂ) • sandwich W ρ -
      sandwich (U - W) ρ).PosSemidef := by
  rw [sandwich_parallelogram]
  exact sandwich_posSemidef (U + W) hρ

end Matrices

/-- The scalar tensor-word sum in the Schatten estimate.  The index type is
arbitrary and the length may be zero.  This is `Fintype.sum_pow` oriented as it
appears in the manuscript. -/
theorem sum_word_products {ι R : Type*} [Fintype ι] [CommSemiring R]
    (weight : ι → R) (m : ℕ) :
    (∑ word : Fin m → ι, ∏ position : Fin m, weight (word position)) =
      (∑ i, weight i) ^ m := by
  classical
  exact (Fintype.sum_pow weight m).symm

end ChannelContinuity
