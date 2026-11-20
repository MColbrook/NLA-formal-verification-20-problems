module

public import NLA.IV04.PaperDenseContinuantDeterminantDefinitions
public import NLA.IV04.PaperDenseContinuantProjectionComplete
public import NLA.IV04.PaperDenseContinuantProjectionPoly
public import NLA.IV04.PaperIntegerContinuantMachineDeterminant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem polynomial_dense_integer_determinant_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialDenseIntegerDeterminant (v 0) :=
  (Cobham.comp polynomial_integer_continuant_cobham
    fun _ : Fin 1 => polynomial_dense_continuant_rows_cobham).of_eq fun _ => rfl

theorem polynomial_dense_integer_determinant_mem_fp : polynomialDenseIntegerDeterminant ∈ FP :=
  CobhamFP_subset_FP polynomial_dense_integer_determinant_cobham

theorem row_projection_reference_row_value (size i : ℕ) (words : List (List Bool)) :
    integerContinuantRowValue (rowProjectionReferenceRow size i words)=
      (denseWordDiagonal size words i,
        if i=0 then 0 else denseWordLower size words i,
        if i=0 then 0 else denseWordUpper size words (i-1)) := by
  by_cases hz : i=0
  · subst i;simp [rowProjectionReferenceRow,integerContinuantRowValue,integerContinuantRow,
      denseWordDiagonal,signedWordValue,firstBit,wordValue,bitValue]
  · have he : i-1+1=i := by omega
    simp [rowProjectionReferenceRow,integerContinuantRowValue,integerContinuantRow,
      denseWordDiagonal,denseWordLower,denseWordUpper,hz,he]

theorem dense_reference_prefix_numeric_run (size count : ℕ) (words : List (List Bool)) :
    integerContinuantNumericRun
      (((List.range count).map (fun i => rowProjectionReferenceRow size i words)).map integerContinuantRowValue) 1 0=
      (integerContinuantValue (denseWordDiagonal size words) (denseWordLower size words)
        (denseWordUpper size words) count,
       if count=0 then 0 else integerContinuantValue (denseWordDiagonal size words)
         (denseWordLower size words) (denseWordUpper size words) (count-1)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [List.range_succ,List.map_append,List.map_singleton]
    rw [integer_continuant_numeric_run_append,ih,row_projection_reference_row_value]
    cases count with
    | zero => simp [integerContinuantNumericRun,integerContinuantValue]
    | succ count => simp [integerContinuantNumericRun,integerContinuantValue]

theorem dense_integer_determinant_word_code (dimension : List Bool) (words : List (List Bool))
    (hk : wordValue dimension ≤ (pair dimension (payloadListCode words)).length) :
    signedWordValue (polynomialDenseIntegerDeterminant (pair dimension (payloadListCode words)))=
      integerContinuantValue (denseWordDiagonal (wordValue dimension) words)
        (denseWordLower (wordValue dimension) words) (denseWordUpper (wordValue dimension) words)
        (wordValue dimension) := by
  rw [polynomialDenseIntegerDeterminant,dense_continuant_rows_word_code dimension words hk,
    integer_continuant_code_value]
  exact congrArg Prod.fst (dense_reference_prefix_numeric_run (wordValue dimension) (wordValue dimension) words)

theorem dense_integer_determinant_square_code (n : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) :
    signedWordValue (polynomialDenseIntegerDeterminant (pair n.bits (payloadListCode words)))=
      integerContinuantValue (denseWordDiagonal n words) (denseWordLower n words) (denseWordUpper n words) n := by
  rw [polynomialDenseIntegerDeterminant,dense_continuant_rows_square_code n words hsize,integer_continuant_code_value]
  exact congrArg Prod.fst (dense_reference_prefix_numeric_run n n words)

theorem dense_integer_determinant_rational (n D : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients (denseWordDiagonal n words) D)
      (commonDenominatorCoefficients (denseWordLower n words) D)
      (commonDenominatorCoefficients (denseWordUpper n words) D)).det=
      (signedWordValue (polynomialDenseIntegerDeterminant (pair n.bits (payloadListCode words))) : ℚ)/(D : ℚ)^n := by
  rw [dense_integer_determinant_square_code n words hsize]
  exact common_denominator_determinant n _ _ _ D hD

#print axioms dense_integer_determinant_rational
end IV04.Paper.Computational