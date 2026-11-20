module

public import NLA.IV04.PaperDenseContinuantDeterminant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem verified_polynomial_dense_continuant_rows_mem_fp : polynomialDenseContinuantRows ∈ FP := by
  exact polynomial_dense_continuant_rows_mem_fp

theorem verified_row_projection_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((rowProjectionStep^[k]) (rowProjectionInitial input)).length ≤
      2*input.length+6+(10*input.length+20)*k := by
  exact row_projection_initial_iterate_length k input

theorem verified_row_projection_diagonal_index_value (d i : List Bool) :
    wordValue (rowProjectionDiagonalIndex d i)=wordValue i*wordValue d+wordValue i := by
  exact row_projection_diagonal_index_value d i

theorem verified_row_projection_lower_index_value (d i : List Bool) :
    wordValue (rowProjectionLowerIndex d i)=wordValue i*wordValue d+(wordValue i-1) := by
  exact row_projection_lower_index_value d i

theorem verified_row_projection_previous_upper_index_value (d i : List Bool) :
    wordValue (rowProjectionPreviousUpperIndex d i)=(wordValue i-1)*wordValue d+wordValue i := by
  exact row_projection_previous_upper_index_value d i

theorem verified_row_projection_row_code (d i : List Bool) (words : List (List Bool)) :
    rowProjectionRow d i (payloadListCode words)=rowProjectionReferenceRow (wordValue d) (wordValue i) words := by
  exact row_projection_row_code d i words

theorem verified_dense_continuant_rows_word_code (dimension : List Bool) (words : List (List Bool))
    (hk : wordValue dimension ≤ (pair dimension (payloadListCode words)).length) :
    polynomialDenseContinuantRows (pair dimension (payloadListCode words))=
      payloadListCode (denseContinuantReferenceRows (wordValue dimension) words) := by
  exact dense_continuant_rows_word_code dimension words hk

theorem verified_dense_continuant_rows_square_code (n : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) :
    polynomialDenseContinuantRows (pair n.bits (payloadListCode words))=
      payloadListCode (denseContinuantReferenceRows n words) := by
  exact dense_continuant_rows_square_code n words hsize

theorem verified_polynomial_dense_integer_determinant_mem_fp : polynomialDenseIntegerDeterminant ∈ FP := by
  exact polynomial_dense_integer_determinant_mem_fp

theorem verified_dense_reference_prefix_numeric_run (size count : ℕ) (words : List (List Bool)) :
    integerContinuantNumericRun
      (((List.range count).map (fun i => rowProjectionReferenceRow size i words)).map integerContinuantRowValue) 1 0=
      (integerContinuantValue (denseWordDiagonal size words) (denseWordLower size words)
        (denseWordUpper size words) count,
       if count=0 then 0 else integerContinuantValue (denseWordDiagonal size words)
         (denseWordLower size words) (denseWordUpper size words) (count-1)) := by
  exact dense_reference_prefix_numeric_run size count words

theorem verified_dense_integer_determinant_word_code (dimension : List Bool) (words : List (List Bool))
    (hk : wordValue dimension ≤ (pair dimension (payloadListCode words)).length) :
    signedWordValue (polynomialDenseIntegerDeterminant (pair dimension (payloadListCode words)))=
      integerContinuantValue (denseWordDiagonal (wordValue dimension) words)
        (denseWordLower (wordValue dimension) words) (denseWordUpper (wordValue dimension) words)
        (wordValue dimension) := by
  exact dense_integer_determinant_word_code dimension words hk

theorem verified_dense_integer_determinant_square_code (n : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) :
    signedWordValue (polynomialDenseIntegerDeterminant (pair n.bits (payloadListCode words)))=
      integerContinuantValue (denseWordDiagonal n words) (denseWordLower n words) (denseWordUpper n words) n := by
  exact dense_integer_determinant_square_code n words hsize

theorem verified_dense_integer_determinant_rational (n D : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients (denseWordDiagonal n words) D)
      (commonDenominatorCoefficients (denseWordLower n words) D)
      (commonDenominatorCoefficients (denseWordUpper n words) D)).det=
      (signedWordValue (polynomialDenseIntegerDeterminant (pair n.bits (payloadListCode words))) : ℚ)/(D : ℚ)^n := by
  exact dense_integer_determinant_rational n D words hsize hD

#print axioms IV04.Paper.Computational.verified_polynomial_dense_continuant_rows_mem_fp
#print axioms IV04.Paper.Computational.verified_row_projection_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_row_projection_diagonal_index_value
#print axioms IV04.Paper.Computational.verified_row_projection_lower_index_value
#print axioms IV04.Paper.Computational.verified_row_projection_previous_upper_index_value
#print axioms IV04.Paper.Computational.verified_row_projection_row_code
#print axioms IV04.Paper.Computational.verified_dense_continuant_rows_word_code
#print axioms IV04.Paper.Computational.verified_dense_continuant_rows_square_code
#print axioms IV04.Paper.Computational.verified_polynomial_dense_integer_determinant_mem_fp
#print axioms IV04.Paper.Computational.verified_dense_reference_prefix_numeric_run
#print axioms IV04.Paper.Computational.verified_dense_integer_determinant_word_code
#print axioms IV04.Paper.Computational.verified_dense_integer_determinant_square_code
#print axioms IV04.Paper.Computational.verified_dense_integer_determinant_rational
end IV04.Paper.Computational
