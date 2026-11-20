module

public import NLA.IV04.PaperSATMetadataPoly
public import NLA.IV04.PaperEncoding
public import NLA.IV04.PaperPayloadWordMaxSemantics
public import NLA.IV04.PaperNestedPayloadCountSemantics
public import NLA.IV04.PaperSATDigitDefinitions
public import NLA.IV04.PaperSATCNFParserSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

private theorem metadata_word_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

 theorem sat_clause_max_var_fold (clause : SAT.Clause) :
    (clause.map fun lit => lit.var).foldr max 0=clause.maxVar := by
  induction clause with
  | nil => rfl
  | cons lit clause ih => simp [ih]

 theorem sat_clause_max_var_le (clause : SAT.Clause) (n : ℕ)
    (h : ∀ lit ∈ clause, lit.var ≤ n) : clause.maxVar ≤ n := by
  induction clause with
  | nil => simp
  | cons lit clause ih =>
    rw [SAT.Clause.maxVar_cons]
    exact max_le (h lit (by simp)) (ih fun l hl => h l (by simp [hl]))

 theorem sat_clause_max_var_reverse (clause : SAT.Clause) :
    SAT.Clause.maxVar clause.reverse=clause.maxVar := by
  apply le_antisymm
  · apply sat_clause_max_var_le
    intro lit hl
    exact SAT.Clause.var_le_maxVar (List.mem_reverse.mp hl)
  · apply sat_clause_max_var_le
    intro lit hl
    exact SAT.Clause.var_le_maxVar (List.mem_reverse.mpr hl)

 theorem polynomial_sat_clause_maximum_exact (clause : SAT.Clause) :
    polynomialSATClauseMaximum (satClausePayload clause)=clause.maxVar.bits := by
  have h := polynomial_payload_word_max_exact pairFst (clause.map satLiteralPayload)
  simpa [polynomialSATClauseMaximum,satClausePayload,List.map_map,Function.comp_def,
    satLiteralPayload,pairFst_pair,metadata_word_bits_value,sat_clause_max_var_fold] using h

 theorem sat_formula_max_var_fold (formula : SAT.CNF) :
    (formula.map SAT.Clause.maxVar).foldr max 0=formula.maxVar := by
  induction formula with
  | nil => rfl
  | cons clause formula ih => simp [ih]

 theorem polynomial_sat_formula_maximum_exact (formula : SAT.CNF) :
    polynomialSATFormulaMaximum (satFormulaPayload formula)=formula.maxVar.bits := by
  have h := polynomial_payload_word_max_exact polynomialSATClauseMaximum
    (formula.map fun clause => satClausePayload clause.reverse)
  simpa [polynomialSATFormulaMaximum,satFormulaPayload,List.map_map,Function.comp_def,
    polynomial_sat_clause_maximum_exact,metadata_word_bits_value,sat_clause_max_var_reverse,
    sat_formula_max_var_fold] using h

 theorem polynomial_sat_metadata_exact (formula : SAT.CNF) :
    polynomialSATMetadata (satFormulaPayload formula)=
      pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits) := by
  have hc := polynomial_payload_count_exact
    (formula.map fun clause => satClausePayload clause.reverse)
  simp only [List.length_map] at hc
  change polynomialPayloadCount (satFormulaPayload formula)=formula.length.bits at hc
  rw [polynomialSATMetadata,polynomial_sat_formula_maximum_exact,hc,sat_formula_payload_literal_count]
  simp [canonical_word_eq_bits,polynomial_word_add_value,metadata_word_bits_value,
    wordValue,bitValue,satVariables,satLiteralBudget]

 theorem polynomial_sat_input_metadata_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATInputMetadata bits=pair [true]
      (pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits)) := by
  simp only [polynomialSATInputMetadata,polynomial_sat_cnf_parse_exact bits formula h,
    pairFst_pair,pairSnd_pair,polynomial_sat_metadata_exact]

 theorem polynomial_sat_input_metadata_reject (bits : List Bool) (h : SAT.CNF.decode? bits=none) :
    pairFst (polynomialSATInputMetadata bits)=[false] := by
  simpa only [polynomialSATInputMetadata,pairFst_pair] using polynomial_sat_cnf_parse_reject bits h

 theorem sat_input_metadata_actual_polytime : polynomialSATInputMetadata ∈ FP ∧
    (∀ bits formula, SAT.CNF.decode? bits=some formula → polynomialSATInputMetadata bits=pair [true]
      (pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits))) ∧
    (∀ bits, SAT.CNF.decode? bits=none → pairFst (polynomialSATInputMetadata bits)=[false]) :=
  ⟨polynomial_sat_input_metadata_mem_fp,polynomial_sat_input_metadata_exact,
    polynomial_sat_input_metadata_reject⟩

#print axioms polynomial_sat_clause_maximum_exact
#print axioms polynomial_sat_formula_maximum_exact
#print axioms polynomial_sat_metadata_exact
#print axioms polynomial_sat_input_metadata_exact
#print axioms polynomial_sat_input_metadata_reject
#print axioms sat_input_metadata_actual_polytime
end IV04.Paper.Computational
