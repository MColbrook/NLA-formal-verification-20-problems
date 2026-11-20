module

public import NLA.IV04.PaperSATWeightTablePoly
public import NLA.IV04.PaperBoundedPayloadMapSemantics
public import NLA.IV04.PaperBoundedPayloadRepeatSemantics
public import NLA.IV04.PaperSATLiteralWeightBindings
public import NLA.IV04.PaperSATRemainingWeightsSemantics
public import NLA.IV04.PaperWordSubtractionSemantics
public import NLA.IV04.PaperPayloadReverseSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
private theorem sat_table_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem sat_table_ofFn_range {α : Type*} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp
 theorem sat_table_flatten_map {α β : Type*} (l : List α) (f : α → List β) :
    (l.map f).flatten=l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]
 theorem sat_table_range_chunks (n : ℕ) (f : ℕ → List Bool) :
    (List.range n).reverse.flatMap f=(List.ofFn (fun i : Fin n => f i.val)).reverse.flatten := by
  rw [sat_table_ofFn_range n f,← List.map_reverse]
  exact (sat_table_flatten_map (List.range n).reverse f).symm
 theorem sat_table_payload_flatMap {α : Type*} (l : List α) (f : α → List (List Bool)) :
    l.flatMap (fun a => payloadListCode (f a))=payloadListCode (l.flatMap f) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih,← literal_digits_payload_append]
 theorem sat_table_reverse_flatten {α : Type*} (l : List (List α)) :
    l.reverse.flatMap List.reverse=l.flatten.reverse := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.reverse_cons,List.flatMap_append,ih,List.reverse_append]
 theorem sat_table_map_chunks_exact (f : List Bool → List Bool)
    (ruler query : List Bool) (bound : ℕ) (chunks : Fin bound → List (List Bool))
    (h : bound ≤ ruler.length+1)
    (hc : ∀ i, f (pair query i.val.bits)=payloadListCode (chunks i).reverse) :
    polynomialBoundedPayloadMap f (pair ruler (pair bound.bits query))=
      payloadListCode (List.ofFn chunks).flatten.reverse := by
  rw [polynomial_bounded_payload_map_exact f ruler query bound h,sat_table_range_chunks]
  have he : List.ofFn (fun i : Fin bound => f (pair query i.val.bits))=
      (List.ofFn chunks).map (fun c => payloadListCode c.reverse) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact hc i
  rw [he,← List.map_reverse,sat_table_flatten_map,sat_table_payload_flatMap,sat_table_reverse_flatten]
 theorem polynomial_sat_table_metadata_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATTableMetadata bits=pair (satVariables formula).bits
      (pair formula.length.bits (satLiteralBudget formula).bits) := by
  simp only [polynomialSATTableMetadata,polynomial_sat_cnf_parse_exact bits formula h,
    pairSnd_pair,polynomial_sat_metadata_exact]
 theorem polynomial_sat_slack_copies_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSlackCopies bits=(satClauseTarget formula-1).bits := by
  simp [polynomialSATSlackCopies,polynomial_sat_table_metadata_exact bits formula h,
    canonical_word_eq_bits,polynomial_word_sub_value,canonical_word_multiply_value,
    sat_table_bits_value,wordValue,bitValue,satClauseTarget]
 theorem polynomial_sat_table_count_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) : polynomialSATTableCount bits=(satSlotCount formula).bits := by
  simp [polynomialSATTableCount,polynomial_sat_table_metadata_exact bits formula h,
    polynomial_sat_slack_copies_exact bits formula h,canonical_word_eq_bits,
    polynomial_word_add_value,canonical_word_multiply_value,sat_table_bits_value,
    wordValue,bitValue,satSlotCount]
 theorem polynomial_sat_literal_chunk_exact (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATLiteralChunk (pair bits v.val.bits)=
      payloadListCode (List.ofFn (fun b : Fin 2 =>
        (satSubsetWeights formula (Sum.inl (v,boolFinTwo.symm b))).bits)).reverse := by
  simp [polynomialSATLiteralChunk,pairFst_pair,pairSnd_pair,
    polynomial_sat_literal_weight_exact bits formula v true h,
    polynomial_sat_literal_weight_exact bits formula v false h,List.ofFn_succ,boolFinTwo,payloadListCode]
 theorem polynomial_sat_slack_chunk_exact (bits : List Bool) (formula : SAT.CNF)
    (j : Fin formula.length) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSlackChunk (pair bits j.val.bits)=
      payloadListCode (List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
        (satSubsetWeights formula (Sum.inr (j,k))).bits)).reverse := by
  have hb : satClauseTarget formula-1 ≤ (smash (false::bits) (false::bits)).length+1 := by
    have hk := sat_clause_target_source_bound formula
    rw [← SAT.CNF.decode?_sound h] at hk
    simp only [smash_length,List.length_cons,pow_two] at hk ⊢
    omega
  have he : List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
      (satSubsetWeights formula (Sum.inr (j,k))).bits)=
      List.replicate (satClauseTarget formula-1) (polynomialSATSlackWeight (pair bits j.val.bits)) := by
    have hw : (fun k : Fin (satClauseTarget formula-1) =>
        (satSubsetWeights formula (Sum.inr (j,k))).bits)=
        (fun _ : Fin (satClauseTarget formula-1) => polynomialSATSlackWeight (pair bits j.val.bits)) := by
      funext k
      exact (polynomial_sat_slack_weight_exact bits formula j k h).symm
    exact (congrArg List.ofFn hw).trans (remaining_weights_constant_of_fn
      (satClauseTarget formula-1) (polynomialSATSlackWeight (pair bits j.val.bits)))
  have hr := polynomial_bounded_payload_repeat_exact
    (smash (false::bits) (false::bits)) (polynomialSATSlackWeight (pair bits j.val.bits))
    (satClauseTarget formula-1) hb
  rw [polynomialSATSlackChunk,pairFst_pair,polynomial_sat_slack_copies_exact bits formula h,hr,he]
  simp only [List.reverse_replicate]
#print axioms polynomial_sat_table_count_exact
#print axioms polynomial_sat_literal_chunk_exact
#print axioms polynomial_sat_slack_chunk_exact
end IV04.Paper.Computational
