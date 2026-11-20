module

public import NLA.IV04.PaperSATClauseCoefficientsSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper.Computational
open Complexity SATReduction
theorem verified_literal_match_clock_length : ∀ (clock input : List Bool),
  ((literalMatchStep^[clock.length]) (literalMatchPack (pairFst input) [] (pairSnd input))).length ≤
      2*input.length+4+4*clock.length := literal_match_clock_length

theorem verified_polynomial_literal_match_count_mem_fp : polynomialLiteralMatchCount ∈ FP := polynomial_literal_match_count_mem_fp

theorem verified_polynomial_literal_match_count_length : ∀ (input : List Bool),
  (polynomialLiteralMatchCount input).length ≤ 6*input.length+4 := polynomial_literal_match_count_length

theorem verified_literal_match_flag_raw : ∀ (literal query : List Bool),
  literalMatchFlag literal query=[decide (wordValue (pairFst literal)=wordValue (pairFst query) ∧
      firstBit (pairSnd literal)=firstBit (pairSnd query))] := literal_match_flag_raw

theorem verified_literal_match_flag_encoded : ∀ (lit : SAT.Lit) (v : ℕ) (b : Bool),
  literalMatchFlag (satLiteralPayload lit) (pair v.bits [b])=[decide (lit.var=v ∧ lit.sign=b)] := literal_match_flag_encoded

theorem verified_polynomial_literal_match_count_exact : ∀ (clause : SAT.Clause) (v : ℕ) (b : Bool),
  polynomialLiteralMatchCount (pair (satClausePayload clause) (pair v.bits [b]))=
      (literalCount clause v b).bits := polynomial_literal_match_count_exact

theorem verified_literal_count_reverse : ∀ (clause : SAT.Clause) (v : ℕ) (b : Bool),
  literalCount clause.reverse v b=literalCount clause v b := literal_count_reverse

theorem verified_sat_literal_match_actual_polytime : polynomialLiteralMatchCount ∈ FP ∧
    (∀ input, (polynomialLiteralMatchCount input).length ≤ 6*input.length+4) ∧
    (∀ clause v b, polynomialLiteralMatchCount (pair (satClausePayload clause) (pair v.bits [b]))=
      (literalCount clause v b).bits) := sat_literal_match_actual_polytime

theorem verified_clause_coefficient_clock_length : ∀ (clock input : List Bool),
  ((clauseCoefficientStep^[clock.length])
      (clauseCoefficientPack (pairFst input) (pairSnd input) [])).length ≤
        24*input.length+4+(12*input.length+34)*clock.length := clause_coefficient_clock_length

theorem verified_polynomial_sat_clause_coefficients_length : ∀ (input : List Bool),
  (polynomialSATClauseCoefficients input).length ≤
      24*input.length+4+(12*input.length+34)*input.length := polynomial_sat_clause_coefficients_length

theorem verified_polynomial_sat_clause_coefficients_mem_fp : polynomialSATClauseCoefficients ∈ FP := polynomial_sat_clause_coefficients_mem_fp

theorem verified_polynomial_sat_clause_coefficients_code : ∀ (payloads : List (List Bool)) (query : List Bool),
  polynomialSATClauseCoefficients (pair (payloadListCode payloads) query)=
      payloadListCode ((payloads.map fun clause => polynomialLiteralMatchCount (pair clause query)).reverse) := polynomial_sat_clause_coefficients_code

theorem verified_polynomial_sat_clause_coefficients_exact : ∀ (formula : SAT.CNF) (v : ℕ) (b : Bool),
  polynomialSATClauseCoefficients (pair (satFormulaPayload formula) (pair v.bits [b]))=
      payloadListCode ((formula.map fun clause => (literalCount clause v b).bits).reverse) := polynomial_sat_clause_coefficients_exact

theorem verified_sat_clause_coefficients_actual_polytime : polynomialSATClauseCoefficients ∈ FP ∧
    (∀ input, (polynomialSATClauseCoefficients input).length ≤
      24*input.length+4+(12*input.length+34)*input.length) ∧
    (∀ formula v b, polynomialSATClauseCoefficients (pair (satFormulaPayload formula) (pair v.bits [b]))=
      payloadListCode ((formula.map fun clause => (literalCount clause v b).bits).reverse)) := sat_clause_coefficients_actual_polytime

#print axioms IV04.Paper.Computational.verified_literal_match_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_literal_match_count_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_literal_match_count_length
#print axioms IV04.Paper.Computational.verified_literal_match_flag_raw
#print axioms IV04.Paper.Computational.verified_literal_match_flag_encoded
#print axioms IV04.Paper.Computational.verified_polynomial_literal_match_count_exact
#print axioms IV04.Paper.Computational.verified_literal_count_reverse
#print axioms IV04.Paper.Computational.verified_sat_literal_match_actual_polytime
#print axioms IV04.Paper.Computational.verified_clause_coefficient_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_coefficients_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_coefficients_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_coefficients_code
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_coefficients_exact
#print axioms IV04.Paper.Computational.verified_sat_clause_coefficients_actual_polytime
end IV04.Paper.Computational
end
