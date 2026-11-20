module

public import NLA.IV04.PaperSATClauseCoefficientsPoly
public import NLA.IV04.PaperSATLiteralMatchSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
 theorem clause_coefficient_iterate_nil (k : ℕ) (query output : List Bool) :
    (clauseCoefficientStep^[k]) (clauseCoefficientPack [] query output)=
      clauseCoefficientPack [] query output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,clause_coefficient_step_pair];simp
 theorem clause_coefficient_iteration_code (k : ℕ) (payloads output : List (List Bool))
    (query : List Bool) (h : payloads.length ≤ k) :
    (clauseCoefficientStep^[k]) (clauseCoefficientPack (payloadListCode payloads) query (payloadListCode output))=
      clauseCoefficientPack [] query (payloadListCode
        ((payloads.map fun clause => polynomialLiteralMatchCount (pair clause query)).reverse ++ output)) := by
  induction k generalizing payloads output with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,clause_coefficient_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h;omega
      rw [Function.iterate_succ_apply,clause_coefficient_step_pair]
      have hn : pair payload (payloadListCode payloads)≠[] := by
        intro he;have hl := congrArg List.length he
        simp only [pair_length,List.length_nil] at hl;omega
      simp only [payloadListCode,hn,if_false,pairFst_pair,pairSnd_pair]
      have hi := ih payloads (polynomialLiteralMatchCount (pair payload query)::output) ht
      simp only [payloadListCode] at hi
      rw [hi]
      simp [List.reverse_cons,List.append_assoc]
 theorem polynomial_sat_clause_coefficients_code (payloads : List (List Bool)) (query : List Bool) :
    polynomialSATClauseCoefficients (pair (payloadListCode payloads) query)=
      payloadListCode ((payloads.map fun clause => polynomialLiteralMatchCount (pair clause query)).reverse) := by
  have hp := payload_list_count_length payloads
  have hs := pairFst_length_le (pair (payloadListCode payloads) query)
  simp only [pairFst_pair] at hs
  have h := clause_coefficient_iteration_code (pair (payloadListCode payloads) query).length payloads [] query (hp.trans hs)
  simpa only [polynomialSATClauseCoefficients,clauseCoefficientState,pairFst_pair,pairSnd_pair,
    payloadListCode,List.append_nil,clauseCoefficientPack] using congrArg (fun s => pairSnd (pairSnd s)) h
 theorem polynomial_sat_clause_coefficients_exact (formula : SAT.CNF) (v : ℕ) (b : Bool) :
    polynomialSATClauseCoefficients (pair (satFormulaPayload formula) (pair v.bits [b]))=
      payloadListCode ((formula.map fun clause => (literalCount clause v b).bits).reverse) := by
  rw [satFormulaPayload,polynomial_sat_clause_coefficients_code]
  simp only [List.map_map,Function.comp_def,polynomial_literal_match_count_exact,literal_count_reverse]
 theorem sat_clause_coefficients_actual_polytime : polynomialSATClauseCoefficients ∈ FP ∧
    (∀ input, (polynomialSATClauseCoefficients input).length ≤
      24*input.length+4+(12*input.length+34)*input.length) ∧
    (∀ formula v b, polynomialSATClauseCoefficients (pair (satFormulaPayload formula) (pair v.bits [b]))=
      payloadListCode ((formula.map fun clause => (literalCount clause v b).bits).reverse)) :=
  ⟨polynomial_sat_clause_coefficients_mem_fp,polynomial_sat_clause_coefficients_length,
    polynomial_sat_clause_coefficients_exact⟩
#print axioms polynomial_sat_clause_coefficients_exact
#print axioms sat_clause_coefficients_actual_polytime
end IV04.Paper.Computational
