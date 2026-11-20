module

public import NLA.IV04.PaperSATCNFPayloadDefinitions
public import NLA.IV04.PaperSATCNFParserBounds
public import NLA.IV04.PaperPayloadReverseSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem sat_cnf_data_token_step (b : Bool) (rest raw clause formula : List Bool) :
    satCNFParseStep (satCNFPack (b::b::rest) raw clause formula [true])=
      satCNFPack rest (raw++[b]) clause formula [true] := by
  simp [sat_cnf_step_pair]

 theorem sat_cnf_literal_token_step (lit : SAT.Lit) (rest : List Bool)
    (clause : SAT.Clause) (formula : SAT.CNF) :
    satCNFParseStep (satCNFPack (false::true::rest) lit.encodeRaw
      (satClausePayload clause) (satFormulaPayload formula) [true])=
      satCNFPack rest [] (satClausePayload (lit::clause)) (satFormulaPayload formula) [true] := by
  simp [sat_cnf_step_pair,polynomial_sat_raw_literal_encoded,satLiteralPayload,
    satClausePayload,payloadListCode,andBit,caseBit₀]

 theorem sat_cnf_clause_token_step (rest : List Bool) (clause : SAT.Clause) (formula : SAT.CNF) :
    satCNFParseStep (satCNFPack (true::false::rest) []
      (satClausePayload clause) (satFormulaPayload formula) [true])=
      satCNFPack rest [] [] (satFormulaPayload (clause.reverse::formula)) [true] := by
  simp [sat_cnf_step_pair,satFormulaPayload,satClausePayload,payloadListCode,
    notBit,nonemptyFlag,andBit,caseBit₀]

 theorem sat_cnf_invalid_step (bits raw clause formula : List Bool) :
    ∃ u c f : List Bool,
      satCNFParseStep (satCNFPack bits raw clause formula [false])=
        satCNFPack bits.tail.tail u c f [false] := by
  cases bits with
  | nil => exact ⟨raw,clause,formula,sat_cnf_step_nil _ _ _ _⟩
  | cons a tail =>
    cases tail with
    | nil => exact ⟨raw,clause,formula,sat_cnf_step_single _ _ _ _ _⟩
    | cons b rest =>
      rw [sat_cnf_step_pair]
      cases a <;> cases b
      · exact ⟨raw++[false],clause,formula,rfl⟩
      · exact ⟨[],pair (pairSnd (polynomialSATRawLiteral raw)) clause,formula,rfl⟩
      · exact ⟨[],[],pair clause formula,rfl⟩
      · exact ⟨raw++[true],clause,formula,rfl⟩

 theorem sat_cnf_invalid_iterate (k : ℕ) (bits raw clause formula : List Bool) :
    ∃ r u c f : List Bool,
      (satCNFParseStep^[k]) (satCNFPack bits raw clause formula [false])=
        satCNFPack r u c f [false] := by
  induction k with
  | zero => exact ⟨bits,raw,clause,formula,rfl⟩
  | succ k ih =>
    obtain ⟨r,u,c,f,he⟩ := ih
    obtain ⟨u',c',f',hs⟩ := sat_cnf_invalid_step r u c f
    refine ⟨r.tail.tail,u',c',f',?_⟩
    rw [Function.iterate_succ_apply',he,hs]

 theorem sat_cnf_invalid_final_flag (k : ℕ) (bits raw clause formula : List Bool) :
    satCNFFinalFlag ((satCNFParseStep^[k]) (satCNFPack bits raw clause formula [false]))=[false] := by
  obtain ⟨r,u,c,f,he⟩ := sat_cnf_invalid_iterate k bits raw clause formula
  rw [he]
  simp [satCNFFinalFlag,satCNFValid,satCNFPack,andBit,caseBit₀]

 theorem sat_cnf_completed_formula_output (formula : SAT.CNF) :
    polynomialPayloadReverse (satFormulaPayload formula)=satFormulaPayload formula.reverse := by
  simp only [satFormulaPayload,payload_reverse_code,List.map_reverse]

#print axioms sat_cnf_data_token_step
#print axioms sat_cnf_literal_token_step
#print axioms sat_cnf_clause_token_step
#print axioms sat_cnf_invalid_final_flag
#print axioms sat_cnf_completed_formula_output
end IV04.Paper.Computational
