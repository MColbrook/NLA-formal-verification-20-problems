module

public import NLA.IV04.PaperSATLiteralDigitsPoly
public import NLA.IV04.PaperSATVariableMarkersSemantics
public import NLA.IV04.PaperSATClauseCoefficientsSemantics
public import NLA.IV04.PaperSATMetadataSemantics
public import NLA.IV04.PaperSATPartitionSize
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
private theorem literal_digits_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem literal_digits_payload_append (left right : List (List Bool)) :
    payloadListCode (left++right)=payloadListCode left++payloadListCode right := by
  induction left with
  | nil => rfl
  | cons word left ih => simp [payloadListCode,ih,pair,List.append_assoc]
 theorem sat_variables_le_decoded_input (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) : satVariables formula ≤ bits.length+1 := by
  rw [SAT.CNF.decode?_sound h]
  exact sat_variables_le_input_length formula
 theorem polynomial_sat_literal_digits_exact (bits : List Bool) (formula : SAT.CNF)
    (v : ℕ) (b : Bool) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATLiteralDigits (pair bits (pair v.bits [b]))=
      payloadListCode (((formula.map fun clause => (literalCount clause v b).bits).reverse) ++
        (((List.range (satVariables formula)).map fun i => if i=v then [true] else []).reverse)) := by
  have hv := sat_variables_le_decoded_input bits formula h
  simp only [polynomialSATLiteralDigits,pairFst_pair,pairSnd_pair,
    polynomial_sat_cnf_parse_exact bits formula h,polynomial_sat_metadata_exact,
    polynomial_sat_clause_coefficients_exact,polynomial_sat_variable_markers_exact bits (satVariables formula) v hv]
  rw [literal_digits_payload_append]
 theorem polynomial_sat_digit_base_exact (formula : SAT.CNF) :
    polynomialSATDigitBase (satFormulaPayload formula)=(satDigitBase formula).bits := by
  simp only [polynomialSATDigitBase,polynomial_sat_metadata_exact,pairFst_pair,pairSnd_pair,
    canonical_word_eq_bits,polynomial_word_add_value,canonical_word_multiply_value,literal_digits_bits_value]
  simp [wordValue,bitValue,satDigitBase,satClauseTarget,Nat.mul_comm]
#print axioms polynomial_sat_literal_digits_exact
#print axioms polynomial_sat_digit_base_exact
end IV04.Paper.Computational
