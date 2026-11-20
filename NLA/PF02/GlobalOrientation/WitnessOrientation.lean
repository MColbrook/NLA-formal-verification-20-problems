module

public import NLA.PF02.GlobalOrientation.ReflectedWitness
public import NLA.PF02.GlobalOrientation.ActualNonzero
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02PositiveBasis
open Reference.PF02BlockSupportRecovery
open scoped BigOperators MatrixOrder

theorem canonical_leading_frame_orthonormal (r : ℕ) :
    (canonicalLeadingFrame r).transpose * canonicalLeadingFrame r = 1 := by
  let R := Matrix.fromRows (1 : Matrix (Fin 3) (Fin 3) ℝ) (0 : Matrix (Fin r) (Fin 3) ℝ)
  change R.transpose.submatrix id finSumFinEquiv.symm * R.submatrix finSumFinEquiv.symm id = 1
  rw [Matrix.submatrix_mul_equiv R.transpose R id finSumFinEquiv.symm id]
  simp [R, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromRows]

theorem canonical_leading_frame_lift (r : ℕ) (C : Matrix (Fin 3) (Fin 3) ℝ) :
    canonicalLeadingFrame r * C * (canonicalLeadingFrame r).transpose =
      (leadingEmbed (r := r) C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  let R := Matrix.fromRows (1 : Matrix (Fin 3) (Fin 3) ℝ) (0 : Matrix (Fin r) (Fin 3) ℝ)
  have he : canonicalLeadingFrame r * C * (canonicalLeadingFrame r).transpose =
      (R * C * R.transpose).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [Matrix.submatrix_mul _ _ finSumFinEquiv.symm id finSumFinEquiv.symm Function.bijective_id,
      Matrix.submatrix_mul _ _ finSumFinEquiv.symm id id Function.bijective_id]
    rfl
  rw [he]
  congr 1
  simp [R, Matrix.transpose_fromRows, leadingEmbed]
  ext (a|a) (b|b) <;> rfl

theorem actual_witness_orientation_opposite (r : ℕ) :
    orientationPolynomial (leadingRows (enumeratedReflectedFactor r)) =
      -orientationPolynomial (leadingRows (enumeratedFactor r)) := by
  have hlead : leadingRows (enumeratedFactor r) =
      (fun p => canonicalLeadingFrame r * positiveMatrix p * (canonicalLeadingFrame r).transpose) := by
    funext p
    rw [canonical_leading_frame_lift]
    simp [leadingRows, blockRows, enumeratedFactor, finiteBlockFactor, blockFactor]
  have href : leadingRows (enumeratedReflectedFactor r) =
      (fun p => canonicalLeadingFrame r * reflectedPositive p * (canonicalLeadingFrame r).transpose) := by
    funext p
    rw [canonical_leading_frame_lift]
    simp [leadingRows, blockRows, enumeratedReflectedFactor, finiteReflectedBlockFactor, reflectedBlockFactor]
  have hsym : ∀ p, (reflectedPositive p).transpose = reflectedPositive p := by
    intro p
    ext a b
    simpa only [Matrix.transpose_apply, star_trivial] using
      (reflected_positive_posSemidef p).isHermitian.apply a b
  rw [hlead, href, orientation_polynomial_lift _ _ hsym,
    orientation_polynomial_lift _ _ positive_matrix_symmetric]
  have hd : (coordinateRows reflectedPositive).det = -(coordinateRows (positiveMatrix (n := 3))).det := by
    rw [show reflectedPositive = (fun p => entryReflection (0 : Fin 3) 1 (positiveMatrix p)) from
      funext reflected_positive_eq]
    exact coordinate_reflection_det _ reflectedPair (by decide)
  rw [hd]
  ring

theorem actual_witness_orientation_product_negative (r : ℕ) :
    orientationPolynomial (leadingRows (enumeratedFactor r)) *
      orientationPolynomial (leadingRows (enumeratedReflectedFactor r)) < 0 := by
  have hn := actual_orientation_polynomial_ne_zero
    (⟨(enumeratedFactor r,enumeratedFactor r), enumerated_factorization r⟩ :
      NLA.PF02.Factorization (enumeratedRealGram r) (3+r))
  change orientationPolynomial (leadingRows (enumeratedFactor r)) ≠ 0 at hn
  rw [actual_witness_orientation_opposite]
  nlinarith [sq_pos_of_ne_zero hn]

#print axioms canonical_leading_frame_orthonormal
#print axioms canonical_leading_frame_lift
#print axioms actual_witness_orientation_opposite
#print axioms actual_witness_orientation_product_negative
end Reference.PF02GlobalOrientation
