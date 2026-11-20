module

public import NLA.IV04.PaperSATLiteralMatchPoly
public import NLA.IV04.PaperSATCNFPayloadDefinitions
public import NLA.IV04.PaperSATDigitDefinitions
public import NLA.IV04.PaperWordListProductSemantics
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

private theorem literal_match_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

 theorem literal_match_flag_raw (literal query : List Bool) :
    literalMatchFlag literal query=[decide (wordValue (pairFst literal)=wordValue (pairFst query) ∧
      firstBit (pairSnd literal)=firstBit (pairSnd query))] := by
  simp only [literalMatchFlag,polynomial_word_le_value,head_flag]
  cases ha : firstBit (pairSnd literal) <;> cases hb : firstBit (pairSnd query) <;>
    by_cases hl : wordValue (pairFst literal) ≤ wordValue (pairFst query) <;>
    by_cases hr : wordValue (pairFst query) ≤ wordValue (pairFst literal) <;>
    simp [andBit,notBit,xorFlag,caseBit₀,caseBit,ha,hb,hl,hr] <;> omega

 theorem literal_match_flag_encoded (lit : SAT.Lit) (v : ℕ) (b : Bool) :
    literalMatchFlag (satLiteralPayload lit) (pair v.bits [b])=[decide (lit.var=v ∧ lit.sign=b)] := by
  simp only [literal_match_flag_raw,satLiteralPayload,pairFst_pair,pairSnd_pair,
    literal_match_bits_value]
  cases h : lit.sign <;> cases b <;> simp [firstBit,h]

 theorem literal_match_iterate_nil (k : ℕ) (count query : List Bool) :
    (literalMatchStep^[k]) (literalMatchPack [] count query)=literalMatchPack [] count query := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,literal_match_step_pair];simp

 theorem literal_match_iteration_value (k : ℕ) (clause : SAT.Clause) (v : ℕ) (b : Bool)
    (count : List Bool) (h : clause.length ≤ k) :
    wordValue (pairFst (pairSnd ((literalMatchStep^[k])
      (literalMatchPack (satClausePayload clause) count (pair v.bits [b])))))=
      wordValue count+literalCount clause v b := by
  induction k generalizing clause count with
  | zero =>
    have he : clause=[] := by cases clause <;> simp_all
    simp [he,satClausePayload,payloadListCode,literalMatchPack,literalCount]
  | succ k ih =>
    cases clause with
    | nil =>
      change wordValue (pairFst (pairSnd ((literalMatchStep^[k+1])
        (literalMatchPack [] count (pair v.bits [b])))))=wordValue count+literalCount [] v b
      rw [literal_match_iterate_nil]
      simp [literalMatchPack,literalCount]
    | cons lit clause =>
      have ht : clause.length ≤ k := by simp only [List.length_cons] at h;omega
      rw [Function.iterate_succ_apply,literal_match_step_pair]
      have hn : pair (satLiteralPayload lit) (payloadListCode (clause.map satLiteralPayload))≠[] := by
        intro he
        have hl := congrArg List.length he
        simp only [pair_length,List.length_nil] at hl
        omega
      simp only [satClausePayload,List.map_cons,payloadListCode,hn,if_false,pairSnd_pair,pairFst_pair]
      by_cases hm : lit.var=v ∧ lit.sign=b
      · have hf : literalMatchFlag (satLiteralPayload lit) (pair v.bits [b])=[true] := by
          rw [literal_match_flag_encoded];simp [hm]
        simp only [hf,caseBit₀]
        change wordValue (pairFst (pairSnd ((literalMatchStep^[k])
          (literalMatchPack (satClausePayload clause) (polynomialWordAdd count [true])
            (pair v.bits [b])))))=wordValue count+literalCount (lit::clause) v b
        rw [ih clause (polynomialWordAdd count [true]) ht,polynomial_word_add_value]
        simp [literalCount,hm,wordValue,bitValue] <;> omega
      · have hf : literalMatchFlag (satLiteralPayload lit) (pair v.bits [b])=[false] := by
          rw [literal_match_flag_encoded];simp [hm]
        simp only [hf,caseBit₀]
        change wordValue (pairFst (pairSnd ((literalMatchStep^[k])
          (literalMatchPack (satClausePayload clause) count (pair v.bits [b])))))=
            wordValue count+literalCount (lit::clause) v b
        rw [ih clause count ht]
        simp [literalCount,hm]

 theorem polynomial_literal_match_count_exact (clause : SAT.Clause) (v : ℕ) (b : Bool) :
    polynomialLiteralMatchCount (pair (satClausePayload clause) (pair v.bits [b]))=
      (literalCount clause v b).bits := by
  have hh := payload_list_count_length (clause.map satLiteralPayload)
  simp only [List.length_map] at hh
  have hp := pairFst_length_le (pair (satClausePayload clause) (pair v.bits [b]))
  simp only [pairFst_pair] at hp
  have hc : clause.length ≤ (pair (satClausePayload clause) (pair v.bits [b])).length := hh.trans hp
  have h := literal_match_iteration_value
    (pair (satClausePayload clause) (pair v.bits [b])).length clause v b [] hc
  simp only [wordValue,Nat.zero_add] at h
  simpa only [polynomialLiteralMatchCount,literalMatchState,pairFst_pair,pairSnd_pair,
    canonical_word_eq_bits,h] using congrArg Nat.bits h

 theorem literal_count_reverse (clause : SAT.Clause) (v : ℕ) (b : Bool) :
    literalCount clause.reverse v b=literalCount clause v b := by
  simp [literalCount,List.map_reverse]

 theorem sat_literal_match_actual_polytime : polynomialLiteralMatchCount ∈ FP ∧
    (∀ input, (polynomialLiteralMatchCount input).length ≤ 6*input.length+4) ∧
    (∀ clause v b, polynomialLiteralMatchCount (pair (satClausePayload clause) (pair v.bits [b]))=
      (literalCount clause v b).bits) :=
  ⟨polynomial_literal_match_count_mem_fp,polynomial_literal_match_count_length,
    polynomial_literal_match_count_exact⟩

#print axioms literal_match_flag_encoded
#print axioms polynomial_literal_match_count_exact
#print axioms sat_literal_match_actual_polytime
end IV04.Paper.Computational
