module

public import NLA.IV04.PaperIntegerContinuantMachineDeterminant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_signed_word_pack_nonempty (flag magnitude : List Bool) :
    signedWordPack flag magnitude ≠ [] := by
  exact signed_word_pack_nonempty flag magnitude

theorem verified_polynomial_signed_add_nonempty (left right : List Bool) :
    polynomialSignedAdd left right ≠ [] := by
  exact polynomial_signed_add_nonempty left right

theorem verified_canonical_signed_word_length (bits : List Bool)
    (hc : bits.tail=(signedWordValue bits).natAbs.bits) (hne : bits ≠ []) :
    bits.length=(signedWordValue bits).natAbs.size+1 := by
  exact canonical_signed_word_length bits hc hne

theorem verified_signed_add_magnitude_size (left right : List Bool) :
    (signedWordValue left+signedWordValue right).natAbs.size ≤
      max left.tail.length right.tail.length+1 := by
  exact signed_add_magnitude_size left right

theorem verified_polynomial_signed_add_max_length (left right : List Bool) :
    (polynomialSignedAdd left right).length ≤ max left.tail.length right.tail.length+2 := by
  exact polynomial_signed_add_max_length left right

theorem verified_polynomial_signed_neg_tail_length (bits : List Bool) :
    (polynomialSignedNeg bits).tail.length ≤ bits.tail.length := by
  exact polynomial_signed_neg_tail_length bits

theorem verified_integer_continuant_next_value (row previous before : List Bool) :
    signedWordValue (integerContinuantNext row previous before)=
      signedWordValue (pairFst row)*signedWordValue previous-
        signedWordValue (pairFst (pairSnd row))*signedWordValue (pairSnd (pairSnd row))*signedWordValue before := by
  exact integer_continuant_next_value row previous before

theorem verified_integer_continuant_next_row_value (diagonal lower upper previous before : List Bool) :
    signedWordValue (integerContinuantNext (integerContinuantRow diagonal lower upper) previous before)=
      signedWordValue diagonal*signedWordValue previous-
        signedWordValue lower*signedWordValue upper*signedWordValue before := by
  exact integer_continuant_next_row_value diagonal lower upper previous before

theorem verified_integer_continuant_next_length (row previous before : List Bool) :
    (integerContinuantNext row previous before).length ≤ max previous.length before.length+row.length+4 := by
  exact integer_continuant_next_length row previous before

theorem verified_integer_continuant_next_cobham :
    Cobham fun v : Fin 3 → List Bool => integerContinuantNext (v 0) (v 1) (v 2) := by
  exact integer_continuant_next_cobham

theorem verified_integer_continuant_pack_cobham {n : ℕ}
    {rest previous before : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hp : Cobham previous) (hb : Cobham before) :
    Cobham fun v => integerContinuantPack (rest v) (previous v) (before v) := by
  exact integer_continuant_pack_cobham hr hp hb

theorem verified_integer_continuant_step_pack (rest previous before : List Bool) :
    integerContinuantStep (integerContinuantPack rest previous before)=
      if rest=[] then integerContinuantPack rest previous before else
        integerContinuantPack (pairSnd rest) (integerContinuantNext (pairFst rest) previous before) previous := by
  exact integer_continuant_step_pack rest previous before

theorem verified_integer_continuant_step_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantStep (v 0) := by
  exact integer_continuant_step_cobham

theorem verified_integer_continuant_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantInitial (v 0) := by
  exact integer_continuant_initial_cobham

theorem verified_integer_continuant_step_shape (rest previous before : List Bool) :
    ∃ r p b : List Bool,
      integerContinuantStep (integerContinuantPack rest previous before)=integerContinuantPack r p b ∧
      r.length+max p.length b.length ≤ rest.length+max previous.length before.length+4 := by
  exact integer_continuant_step_shape rest previous before

theorem verified_integer_continuant_iterate_shape (k : ℕ) (rest previous before : List Bool) :
    ∃ r p b : List Bool,
      (integerContinuantStep^[k]) (integerContinuantPack rest previous before)=integerContinuantPack r p b ∧
      r.length+max p.length b.length ≤ rest.length+max previous.length before.length+4*k := by
  exact integer_continuant_iterate_shape k rest previous before

theorem verified_integer_continuant_pack_length (rest previous before : List Bool) :
    (integerContinuantPack rest previous before).length ≤
      3*(rest.length+max previous.length before.length)+4 := by
  exact integer_continuant_pack_length rest previous before

theorem verified_integer_continuant_iterate_length (k : ℕ) (rest previous before : List Bool) :
    ((integerContinuantStep^[k]) (integerContinuantPack rest previous before)).length ≤
      3*(rest.length+max previous.length before.length)+4+12*k := by
  exact integer_continuant_iterate_length k rest previous before

theorem verified_integer_continuant_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((integerContinuantStep^[k]) (integerContinuantInitial input)).length ≤ 3*input.length+10+12*k := by
  exact integer_continuant_initial_iterate_length k input

theorem verified_integer_continuant_state_length (input : List Bool) :
    (integerContinuantState input).length ≤ 15*input.length+10 := by
  exact integer_continuant_state_length input

theorem verified_integer_continuant_state_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantState (v 0) := by
  exact integer_continuant_state_cobham

theorem verified_polynomial_integer_continuant_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialIntegerContinuant (v 0) := by
  exact polynomial_integer_continuant_cobham

theorem verified_polynomial_integer_continuant_mem_fp : polynomialIntegerContinuant ∈ FP := by
  exact polynomial_integer_continuant_mem_fp

theorem verified_integer_continuant_iterate_nil (k : ℕ) (previous before : List Bool) :
    (integerContinuantStep^[k]) (integerContinuantPack [] previous before)=integerContinuantPack [] previous before := by
  exact integer_continuant_iterate_nil k previous before

theorem verified_integer_continuant_iterate_code (k : ℕ) (rows : List (List Bool))
    (previous before : List Bool) (h : rows.length ≤ k) :
    (integerContinuantStep^[k]) (integerContinuantPack (payloadListCode rows) previous before)=
      integerContinuantPack [] (integerContinuantWordRun rows previous before).1
        (integerContinuantWordRun rows previous before).2 := by
  exact integer_continuant_iterate_code k rows previous before h

theorem verified_integer_continuant_code (rows : List (List Bool)) :
    polynomialIntegerContinuant (payloadListCode rows)=(integerContinuantWordRun rows [false,true] [false]).1 := by
  exact integer_continuant_code rows

theorem verified_integer_continuant_word_run_value (rows : List (List Bool)) (previous before : List Bool) :
    (signedWordValue (integerContinuantWordRun rows previous before).1,
      signedWordValue (integerContinuantWordRun rows previous before).2)=
      integerContinuantNumericRun (rows.map integerContinuantRowValue) (signedWordValue previous) (signedWordValue before) := by
  exact integer_continuant_word_run_value rows previous before

theorem verified_integer_continuant_code_value (rows : List (List Bool)) :
    signedWordValue (polynomialIntegerContinuant (payloadListCode rows))=
      (integerContinuantNumericRun (rows.map integerContinuantRowValue) 1 0).1 := by
  exact integer_continuant_code_value rows

theorem verified_integer_continuant_numeric_run_append (rows more : List (ℤ × ℤ × ℤ)) (previous before : ℤ) :
    integerContinuantNumericRun (rows++more) previous before=
      integerContinuantNumericRun more (integerContinuantNumericRun rows previous before).1
        (integerContinuantNumericRun rows previous before).2 := by
  exact integer_continuant_numeric_run_append rows more previous before

theorem verified_integer_continuant_numeric_rows_value (a lower upper : ℕ → ℤ) (n : ℕ) :
    integerContinuantNumericRun (integerContinuantNumericRows a lower upper n) 1 0=
      (integerContinuantValue a lower upper n,if n=0 then 0 else integerContinuantValue a lower upper (n-1)) := by
  exact integer_continuant_numeric_rows_value a lower upper n

theorem verified_integer_continuant_actual_polytime : polynomialIntegerContinuant ∈ FP ∧
    ∀ rows : List (List Bool),
      signedWordValue (polynomialIntegerContinuant (payloadListCode rows))=
        (integerContinuantNumericRun (rows.map integerContinuantRowValue) 1 0).1 := by
  exact integer_continuant_actual_polytime

theorem verified_integer_signed_word_value (value : ℤ) : signedWordValue (integerSignedWord value)=value := by
  exact integer_signed_word_value value

theorem verified_integer_continuant_row_code_value (row : ℤ × ℤ × ℤ) :
    integerContinuantRowValue (integerContinuantRowCode row)=row := by
  exact integer_continuant_row_code_value row

theorem verified_integer_continuant_exact_integer_codes (a lower upper : ℕ → ℤ) (n : ℕ) :
    signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n))=
      integerContinuantValue a lower upper n := by
  exact integer_continuant_exact_integer_codes a lower upper n

theorem verified_integer_continuant_exact_rational_determinant (a lower upper : ℕ → ℤ)
    (n D : ℕ) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D)).det=
      (signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n)) : ℚ)/(D : ℚ)^n := by
  exact integer_continuant_exact_rational_determinant a lower upper n D hD

theorem verified_integer_continuant_exact_codes_polytime : polynomialIntegerContinuant ∈ FP ∧
    ∀ (a lower upper : ℕ → ℤ) (n : ℕ),
      signedWordValue (polynomialIntegerContinuant (integerContinuantRowsCode a lower upper n))=
        integerContinuantValue a lower upper n := by
  exact integer_continuant_exact_codes_polytime

#print axioms IV04.Paper.Computational.verified_signed_word_pack_nonempty
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_nonempty
#print axioms IV04.Paper.Computational.verified_canonical_signed_word_length
#print axioms IV04.Paper.Computational.verified_signed_add_magnitude_size
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_max_length
#print axioms IV04.Paper.Computational.verified_polynomial_signed_neg_tail_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_next_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_next_row_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_next_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_next_cobham
#print axioms IV04.Paper.Computational.verified_integer_continuant_pack_cobham
#print axioms IV04.Paper.Computational.verified_integer_continuant_step_pack
#print axioms IV04.Paper.Computational.verified_integer_continuant_step_cobham
#print axioms IV04.Paper.Computational.verified_integer_continuant_initial_cobham
#print axioms IV04.Paper.Computational.verified_integer_continuant_step_shape
#print axioms IV04.Paper.Computational.verified_integer_continuant_iterate_shape
#print axioms IV04.Paper.Computational.verified_integer_continuant_pack_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_iterate_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_state_length
#print axioms IV04.Paper.Computational.verified_integer_continuant_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_integer_continuant_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_integer_continuant_mem_fp
#print axioms IV04.Paper.Computational.verified_integer_continuant_iterate_nil
#print axioms IV04.Paper.Computational.verified_integer_continuant_iterate_code
#print axioms IV04.Paper.Computational.verified_integer_continuant_code
#print axioms IV04.Paper.Computational.verified_integer_continuant_word_run_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_code_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_numeric_run_append
#print axioms IV04.Paper.Computational.verified_integer_continuant_numeric_rows_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_actual_polytime
#print axioms IV04.Paper.Computational.verified_integer_signed_word_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_row_code_value
#print axioms IV04.Paper.Computational.verified_integer_continuant_exact_integer_codes
#print axioms IV04.Paper.Computational.verified_integer_continuant_exact_rational_determinant
#print axioms IV04.Paper.Computational.verified_integer_continuant_exact_codes_polytime
end IV04.Paper.Computational
