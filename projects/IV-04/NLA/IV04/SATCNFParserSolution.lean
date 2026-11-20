module

public import NLA.IV04.PaperSATCNFParserSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper.Computational
open Complexity
theorem verified_sat_unary_flag_exact : ∀ (bits : List Bool),
  satUnaryFlag bits=[decide (∀ b∈bits,b=true)] := sat_unary_flag_exact

theorem verified_polynomial_sat_raw_literal_mem_fp : polynomialSATRawLiteral ∈ FP := polynomial_sat_raw_literal_mem_fp

theorem verified_actual_sat_raw_literal_decoder : ∀ (input : List Bool),
  decodeSATRawLiteralResult input=Complexity.SAT.Lit.decodeRaw? input := actual_sat_raw_literal_decoder

theorem verified_polynomial_sat_raw_literal_encoded : ∀ (lit : Complexity.SAT.Lit),
  polynomialSATRawLiteral lit.encodeRaw=pair [true] (pair lit.var.bits [lit.sign]) := polynomial_sat_raw_literal_encoded

theorem verified_sat_raw_literal_actual_polytime : polynomialSATRawLiteral ∈ FP ∧
    (∀ input, decodeSATRawLiteralResult input=Complexity.SAT.Lit.decodeRaw? input) ∧
    (∀ lit : Complexity.SAT.Lit,
      polynomialSATRawLiteral lit.encodeRaw=pair [true] (pair lit.var.bits [lit.sign])) := sat_raw_literal_actual_polytime

theorem verified_sat_cnf_parse_clock_length : ∀ (clock input : List Bool),
  ((satCNFParseStep^[clock.length]) (satCNFPack input [] [] [] [true])).length ≤
      2*input.length+9+40*clock.length := sat_cnf_parse_clock_length

theorem verified_polynomial_sat_cnf_parse_mem_fp : polynomialSATCNFParse ∈ FP := polynomial_sat_cnf_parse_mem_fp

theorem verified_polynomial_sat_cnf_parse_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATCNFParse bits=pair [true] (satFormulaPayload formula) := polynomial_sat_cnf_parse_exact

theorem verified_polynomial_sat_cnf_parse_reject : ∀ (bits : List Bool) (h : SAT.CNF.decode? bits=none),
  pairFst (polynomialSATCNFParse bits)=[false] := polynomial_sat_cnf_parse_reject

theorem verified_polynomial_sat_cnf_parse_encoded : ∀ (formula : SAT.CNF),
  polynomialSATCNFParse formula.encode=pair [true] (satFormulaPayload formula) := polynomial_sat_cnf_parse_encoded

theorem verified_sat_cnf_parse_actual_polytime : polynomialSATCNFParse ∈ FP ∧
    (∀ bits formula, SAT.CNF.decode? bits=some formula →
      polynomialSATCNFParse bits=pair [true] (satFormulaPayload formula)) ∧
    (∀ bits, SAT.CNF.decode? bits=none → pairFst (polynomialSATCNFParse bits)=[false]) := sat_cnf_parse_actual_polytime

#print axioms IV04.Paper.Computational.verified_sat_unary_flag_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_raw_literal_mem_fp
#print axioms IV04.Paper.Computational.verified_actual_sat_raw_literal_decoder
#print axioms IV04.Paper.Computational.verified_polynomial_sat_raw_literal_encoded
#print axioms IV04.Paper.Computational.verified_sat_raw_literal_actual_polytime
#print axioms IV04.Paper.Computational.verified_sat_cnf_parse_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_cnf_parse_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_cnf_parse_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_cnf_parse_reject
#print axioms IV04.Paper.Computational.verified_polynomial_sat_cnf_parse_encoded
#print axioms IV04.Paper.Computational.verified_sat_cnf_parse_actual_polytime
end IV04.Paper.Computational
end
