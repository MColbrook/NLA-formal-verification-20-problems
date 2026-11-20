module

public import NLA.IV04.PaperIntegerContinuantMachineSemantics
public import NLA.IV04.PaperContinuantGrowth
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem integer_signed_word_value (value : ℤ) : signedWordValue (integerSignedWord value)=value := by
  cases value with
  | ofNat n => simp [integerSignedWord,signedWordValue,firstBit,word_value_foldr,IV04.Paper.bits_foldr,
      show ¬(n : ℤ)<0 from not_lt.mpr (Int.natCast_nonneg n)]
  | negSucc n =>
    simp [integerSignedWord,signedWordValue,firstBit,word_value_foldr,IV04.Paper.bits_foldr]
    omega

theorem integer_continuant_row_code_value (row : ℤ × ℤ × ℤ) :
    integerContinuantRowValue (integerContinuantRowCode row)=row := by
  simp only [integerContinuantRowValue,integerContinuantRowCode,integerContinuantRow,
    pairFst_pair,pairSnd_pair,integer_signed_word_value]

theorem integer_continuant_exact_integer_codes (a lower upper : ℕ → ℤ) (n : ℕ) :
    signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n))=
      integerContinuantValue a lower upper n := by
  unfold integerContinuantRowsCode
  rw [integer_continuant_code_value]
  have he : ((integerContinuantNumericRows a lower upper n).map integerContinuantRowCode).map
      integerContinuantRowValue=integerContinuantNumericRows a lower upper n := by
    rw [List.map_map]
    have hf : integerContinuantRowValue ∘ integerContinuantRowCode = id := by
      funext row
      exact integer_continuant_row_code_value row
    rw [hf,List.map_id]
  rw [he]
  exact congrArg Prod.fst (integer_continuant_numeric_rows_value a lower upper n)

theorem integer_continuant_exact_rational_determinant (a lower upper : ℕ → ℤ)
    (n D : ℕ) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D)).det=
      (signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n)) : ℚ)/(D : ℚ)^n := by
  rw [integer_continuant_exact_integer_codes]
  exact common_denominator_determinant n a lower upper D hD

theorem integer_continuant_exact_codes_polytime : polynomialIntegerContinuant ∈ FP ∧
    ∀ (a lower upper : ℕ → ℤ) (n : ℕ),
      signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n))=
        integerContinuantValue a lower upper n :=
  ⟨polynomial_integer_continuant_mem_fp,integer_continuant_exact_integer_codes⟩

#print axioms integer_continuant_exact_codes_polytime
end IV04.Paper.Computational
