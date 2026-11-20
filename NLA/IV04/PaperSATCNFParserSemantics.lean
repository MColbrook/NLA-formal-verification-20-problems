module

public import NLA.IV04.PaperSATCNFParserSteps
public import NLA.IV04.PaperSATCNFParserPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

private theorem sat_cnf_not_nonempty (bits : List Bool) :
    notBit (nonemptyFlag bits)=[decide (bits=[])] := by
  cases bits with
  | nil => rfl
  | cons b bits => cases b <;> rfl

 theorem sat_cnf_final_flag_valid_pack (rest raw clause formula : List Bool) :
    satCNFFinalFlag (satCNFPack rest raw clause formula [true])=
      [decide (rest=[] ∧ raw=[] ∧ clause=[])] := by
  simp only [satCNFFinalFlag,satCNFValid,satCNFRest,satCNFRaw,satCNFClause,
    satCNFPack,pairFst_pair,pairSnd_pair,sat_cnf_not_nonempty]
  cases rest <;> cases raw <;> cases clause <;> rfl

 theorem sat_clause_payload_eq_nil (clause : SAT.Clause) :
    satClausePayload clause=[] ↔ clause=[] := by
  cases clause <;> simp [satClausePayload,payloadListCode,payload_pair_ne_nil]

 theorem sat_cnf_iterate_nil (k : ℕ) (raw clause formula valid : List Bool) :
    (satCNFParseStep^[k]) (satCNFPack [] raw clause formula valid)=
      satCNFPack [] raw clause formula valid := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,sat_cnf_step_nil]

 theorem sat_raw_literal_flag (bits : List Bool) :
    pairFst (polynomialSATRawLiteral bits)=[(SAT.Lit.decodeRaw? bits).isSome] := by
  cases bits with
  | nil => rfl
  | cons sign rest =>
    by_cases h : ∀ b∈rest,b=true
    · have hf : satUnaryFlag rest=[true] := by
        simpa only [sat_unary_flag_exact,List.cons.injEq,and_true,decide_eq_true_eq] using h
      have hd : SAT.Lit.decodeRaw? (sign::rest)=some ⟨sign,rest.length⟩ := by
        simp only [SAT.Lit.decodeRaw?,dif_pos h]
      rw [hd]
      cases sign <;> simp [polynomialSATRawLiteral,hf,nonemptyFlag,andBit,caseBit₀,caseBit]
    · have hf : satUnaryFlag rest=[false] := by
        simpa only [sat_unary_flag_exact,List.cons.injEq,and_true,decide_eq_false_iff_not] using h
      have hd : SAT.Lit.decodeRaw? (sign::rest)=none := by
        simp only [SAT.Lit.decodeRaw?,dif_neg h]
      rw [hd]
      cases sign <;> simp [polynomialSATRawLiteral,hf,nonemptyFlag,andBit,caseBit₀,caseBit]

 theorem sat_cnf_actual_from_nil (rawRev : List Bool) (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFActualFrom [] rawRev clauseRev formulaRev=
      if rawRev=[] then (if clauseRev=[] then some formulaRev.reverse else none) else none := rfl

 theorem sat_cnf_actual_from_single (b : Bool) (rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFActualFrom [b] rawRev clauseRev formulaRev=none := rfl

 theorem sat_cnf_actual_from_data (b : Bool) (bits rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFActualFrom (b::b::bits) rawRev clauseRev formulaRev=
      satCNFActualFrom bits (b::rawRev) clauseRev formulaRev := by
  cases b <;> cases ht : SAT.tokenize? bits <;>
    simp [satCNFActualFrom,SAT.tokenize?,ht,SAT.parseTokensAux]

 theorem sat_cnf_actual_from_lit (bits rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFActualFrom (false::true::bits) rawRev clauseRev formulaRev=
      (SAT.Lit.decodeRaw? rawRev.reverse).bind fun lit =>
        satCNFActualFrom bits [] (lit::clauseRev) formulaRev := by
  cases ht : SAT.tokenize? bits <;> cases hl : SAT.Lit.decodeRaw? rawRev.reverse <;>
    simp [satCNFActualFrom,SAT.tokenize?,ht,SAT.parseTokensAux,hl]

 theorem sat_cnf_actual_from_clause (bits rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFActualFrom (true::false::bits) rawRev clauseRev formulaRev=
      if rawRev=[] then satCNFActualFrom bits [] [] (clauseRev.reverse::formulaRev) else none := by
  cases rawRev <;> cases ht : SAT.tokenize? bits <;>
    simp [satCNFActualFrom,SAT.tokenize?,ht,SAT.parseTokensAux]

 theorem sat_cnf_empty_outcome (k : ℕ) (rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    satCNFOutcome (satCNFActualFrom [] rawRev clauseRev formulaRev)
      ((satCNFParseStep^[k]) (satCNFPack [] rawRev.reverse
        (satClausePayload clauseRev) (satFormulaPayload formulaRev) [true])) := by
  rw [sat_cnf_iterate_nil,sat_cnf_actual_from_nil]
  cases rawRev <;> cases clauseRev <;>
    simp only [List.reverse_nil,List.cons_ne_nil,if_true,if_false] <;>
    simp only [satCNFOutcome,sat_cnf_final_flag_valid_pack] <;>
    simp [sat_clause_payload_eq_nil,satCNFFormula,satCNFPack,sat_cnf_completed_formula_output]

 theorem sat_cnf_invalid_literal_token_step (rest raw clause formula : List Bool)
    (h : SAT.Lit.decodeRaw? raw=none) :
    satCNFParseStep (satCNFPack (false::true::rest) raw clause formula [true])=
      satCNFPack rest [] (pair (pairSnd (polynomialSATRawLiteral raw)) clause) formula [false] := by
  rw [sat_cnf_step_pair]
  have hf : pairFst (polynomialSATRawLiteral raw)=[false] := by rw [sat_raw_literal_flag,h];rfl
  simp [hf,andBit,caseBit₀]

 theorem sat_cnf_invalid_clause_token_step (rest raw clause formula : List Bool) (h : raw≠[]) :
    satCNFParseStep (satCNFPack (true::false::rest) raw clause formula [true])=
      satCNFPack rest [] [] (pair clause formula) [false] := by
  rw [sat_cnf_step_pair]
  simp [sat_cnf_not_nonempty,h,andBit,caseBit₀]

/-- Complete physical-input clock proof against the original tokenizer/parser,
    including malformed tokens, odd tails, incomplete literals and clauses. -/
 theorem sat_cnf_parse_clock_semantics (k : ℕ) (bits rawRev : List Bool)
    (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) (hlen : bits.length ≤ k) :
    satCNFOutcome (satCNFActualFrom bits rawRev clauseRev formulaRev)
      ((satCNFParseStep^[k]) (satCNFPack bits rawRev.reverse
        (satClausePayload clauseRev) (satFormulaPayload formulaRev) [true])) := by
  induction k generalizing bits rawRev clauseRev formulaRev with
  | zero =>
    have he : bits=[] := by cases bits <;> simp_all
    subst bits
    exact sat_cnf_empty_outcome 0 rawRev clauseRev formulaRev
  | succ k ih =>
    cases bits with
    | nil => exact sat_cnf_empty_outcome (k+1) rawRev clauseRev formulaRev
    | cons a tail =>
      cases tail with
      | nil =>
        rw [sat_cnf_actual_from_single]
        change satCNFFinalFlag _=[false]
        rw [Function.iterate_succ_apply,sat_cnf_step_single]
        exact sat_cnf_invalid_final_flag k [] _ _ _
      | cons b rest =>
        have ht : rest.length ≤ k := by simp only [List.length_cons] at hlen;omega
        cases a <;> cases b
        · rw [sat_cnf_actual_from_data]
          rw [Function.iterate_succ_apply,sat_cnf_data_token_step]
          simpa only [List.reverse_cons] using ih rest (false::rawRev) clauseRev formulaRev ht
        · rw [sat_cnf_actual_from_lit]
          cases hl : SAT.Lit.decodeRaw? rawRev.reverse with
          | none =>
            simp only [Option.bind_none]
            change satCNFFinalFlag _=[false]
            rw [Function.iterate_succ_apply,sat_cnf_invalid_literal_token_step _ _ _ _ hl]
            exact sat_cnf_invalid_final_flag k rest _ _ _
          | some lit =>
            simp only [Option.bind_some]
            have he : rawRev.reverse=lit.encodeRaw := SAT.Lit.decodeRaw?_sound hl
            rw [Function.iterate_succ_apply,he,sat_cnf_literal_token_step]
            exact ih rest [] (lit::clauseRev) formulaRev ht
        · rw [sat_cnf_actual_from_clause]
          by_cases hz : rawRev=[]
          · subst rawRev
            simp only [if_true]
            rw [Function.iterate_succ_apply]
            change satCNFOutcome _ ((satCNFParseStep^[k])
              (satCNFParseStep (satCNFPack (true::false::rest) []
                (satClausePayload clauseRev) (satFormulaPayload formulaRev) [true])))
            rw [sat_cnf_clause_token_step]
            exact ih rest [] [] (clauseRev.reverse::formulaRev) ht
          · simp only [hz,if_false]
            change satCNFFinalFlag _=[false]
            have hf : rawRev.reverse≠[] := by simpa using hz
            rw [Function.iterate_succ_apply,sat_cnf_invalid_clause_token_step _ _ _ _ hf]
            exact sat_cnf_invalid_final_flag k rest _ _ _
        · rw [sat_cnf_actual_from_data]
          rw [Function.iterate_succ_apply,sat_cnf_data_token_step]
          simpa only [List.reverse_cons] using ih rest (true::rawRev) clauseRev formulaRev ht

 theorem polynomial_sat_cnf_parse_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATCNFParse bits=pair [true] (satFormulaPayload formula) := by
  have he := sat_cnf_parse_clock_semantics bits.length bits [] [] [] (le_refl _)
  change satCNFOutcome (SAT.CNF.decode? bits) (satCNFParseState bits) at he
  rw [h] at he
  obtain ⟨hv,hf⟩ := he
  simp only [polynomialSATCNFParse,hv,hf]

 theorem polynomial_sat_cnf_parse_reject (bits : List Bool) (h : SAT.CNF.decode? bits=none) :
    pairFst (polynomialSATCNFParse bits)=[false] := by
  have he := sat_cnf_parse_clock_semantics bits.length bits [] [] [] (le_refl _)
  change satCNFOutcome (SAT.CNF.decode? bits) (satCNFParseState bits) at he
  rw [h] at he
  simpa only [polynomialSATCNFParse,pairFst_pair,satCNFOutcome] using he

 theorem polynomial_sat_cnf_parse_encoded (formula : SAT.CNF) :
    polynomialSATCNFParse formula.encode=pair [true] (satFormulaPayload formula) :=
  polynomial_sat_cnf_parse_exact formula.encode formula (SAT.CNF.decode?_encode formula)

 theorem sat_cnf_parse_actual_polytime : polynomialSATCNFParse ∈ FP ∧
    (∀ bits formula, SAT.CNF.decode? bits=some formula →
      polynomialSATCNFParse bits=pair [true] (satFormulaPayload formula)) ∧
    (∀ bits, SAT.CNF.decode? bits=none → pairFst (polynomialSATCNFParse bits)=[false]) :=
  ⟨polynomial_sat_cnf_parse_mem_fp,polynomial_sat_cnf_parse_exact,polynomial_sat_cnf_parse_reject⟩

#print axioms polynomial_sat_cnf_parse_encoded
#print axioms polynomial_sat_cnf_parse_exact
#print axioms polynomial_sat_cnf_parse_reject
#print axioms sat_cnf_parse_actual_polytime
end IV04.Paper.Computational
