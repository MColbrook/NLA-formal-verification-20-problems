module

public import NLA.IV04.PaperDenseWordMatrixDefinitions
public import NLA.IV04.PaperDenseContinuantDeterminant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem dense_word_matrix_equals_continuant (n D : ℕ) (words : List (List Bool))
    (htri : RationalTridiagonal (denseWordRationalMatrix n D words)) :
    denseWordRationalMatrix n D words=
      rationalContinuantMatrix n (commonDenominatorCoefficients (denseWordDiagonal n words) D)
        (commonDenominatorCoefficients (denseWordLower n words) D)
        (commonDenominatorCoefficients (denseWordUpper n words) D) := by
  ext i j
  by_cases he : i=j
  · subst j;simp [denseWordRationalMatrix,rationalContinuantMatrix,commonDenominatorCoefficients,denseWordDiagonal]
  · by_cases hu : j.val=i.val+1
    · simp [denseWordRationalMatrix,rationalContinuantMatrix,commonDenominatorCoefficients,denseWordUpper,he,hu]
    · by_cases hl : i.val=j.val+1
      · have hs : i.val-1=j.val := by omega
        simp only [denseWordRationalMatrix,rationalContinuantMatrix,if_neg he,if_neg hu,if_pos hl,
          commonDenominatorCoefficients,denseWordLower]
        rw [hs]
      · have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
        have hbad : i.val+1 < j.val ∨ j.val+1 < i.val := by omega
        simpa [rationalContinuantMatrix,he,hu,hl] using htri i j hbad

theorem dense_word_matrix_determinant (n D : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) (hD : 0 < D)
    (htri : RationalTridiagonal (denseWordRationalMatrix n D words)) :
    (denseWordRationalMatrix n D words).det=
      (signedWordValue (polynomialDenseIntegerDeterminant (Complexity.pair n.bits (payloadListCode words))) : ℚ)/(D : ℚ)^n := by
  rw [dense_word_matrix_equals_continuant n D words htri]
  exact dense_integer_determinant_rational n D words hsize hD

#print axioms dense_word_matrix_determinant
end IV04.Paper.Computational