module

public import NLA.IV04.PaperSATRemainingWeightsPoly
public import NLA.IV04.PaperSATLiteralWeightBindings
public import NLA.IV04.PaperBoundedPayloadRepeatSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
private theorem remaining_weights_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem sat_clauses_le_decoded_input (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) : formula.length ≤ bits.length+1 := by
  rw [SAT.CNF.decode?_sound h]
  exact Nat.le_trans (sat_clauses_le_input_length formula) (Nat.le_succ _)
 theorem polynomial_sat_clause_target_exact (formula : SAT.CNF) :
    polynomialSATClauseTarget (satFormulaPayload formula)=(satClauseTarget formula).bits := by
  simp only [polynomialSATClauseTarget,polynomial_sat_metadata_exact,pairFst_pair,pairSnd_pair,
    canonicalWordMultiply,canonical_word_eq_bits,polynomial_word_multiply_value,remaining_weights_bits_value]
  rfl
 theorem polynomial_sat_slack_digits_exact (bits : List Bool) (formula : SAT.CNF)
    (j : ℕ) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSlackDigits (pair bits j.bits)=
      payloadListCode ((((List.range formula.length).map fun i => if i=j then [true] else []).reverse) ++
        List.replicate (satVariables formula) []) := by
  have hv := sat_variables_le_decoded_input bits formula h
  have hc := sat_clauses_le_decoded_input bits formula h
  simp only [polynomialSATSlackDigits,pairFst_pair,pairSnd_pair,
    polynomial_sat_cnf_parse_exact bits formula h,polynomial_sat_metadata_exact,
    polynomial_sat_variable_markers_exact bits formula.length j hc,
    polynomial_bounded_payload_repeat_exact bits [] (satVariables formula) hv]
  rw [literal_digits_payload_append]
 theorem polynomial_sat_target_digits_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATTargetDigits bits=
      payloadListCode (List.replicate formula.length (satClauseTarget formula).bits ++
        List.replicate (satVariables formula) [true]) := by
  have hv := sat_variables_le_decoded_input bits formula h
  have hc := sat_clauses_le_decoded_input bits formula h
  simp only [polynomialSATTargetDigits,polynomial_sat_cnf_parse_exact bits formula h,pairSnd_pair,
    polynomial_sat_metadata_exact,pairFst_pair,polynomial_sat_clause_target_exact,
    polynomial_bounded_payload_repeat_exact bits (satClauseTarget formula).bits formula.length hc,
    polynomial_bounded_payload_repeat_exact bits [true] (satVariables formula) hv]
  rw [literal_digits_payload_append]
 theorem remaining_weights_fin_marker_bits {n : ℕ} (v : Fin n) :
    (fun u : Fin n => (if v=u then (1 : ℕ) else 0).bits)=
      (fun u : Fin n => if u.val=v.val then [true] else []) := by
  funext u
  by_cases h : v=u
  · subst u;simp
  · have hn : u.val≠v.val := by intro he;exact h (Fin.ext he.symm)
    simp [h,hn]
 theorem remaining_weights_constant_of_fn (n : ℕ) (word : List Bool) :
    List.ofFn (fun _ : Fin n => word)=List.replicate n word := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp
 theorem sat_slack_positional_payloads (formula : SAT.CNF) (j : Fin formula.length)
    (k : Fin (satClauseTarget formula-1)) :
    positionalDigitPayloads (fun t => satWeightDigits formula (Sum.inr (j,k)) (finSumFinEquiv.symm t))=
      (((List.range formula.length).map fun i => if i=j.val then [true] else []).reverse) ++
        List.replicate (satVariables formula) [] := by
  have hd : (fun t => satWeightDigits formula (Sum.inr (j,k)) (finSumFinEquiv.symm t))=
      Fin.append (fun _ : Fin (satVariables formula) => (0 : ℕ))
        (fun l : Fin formula.length => if j=l then 1 else 0) := by
    funext t
    refine Fin.addCases ?_ ?_ t
    · intro v;simp [satWeightDigits]
    · intro l;simp [satWeightDigits]
  simp only [positionalDigitPayloads,hd,List.ofFn_fin_append,List.reverse_append,List.map_append,
    List.map_reverse,List.map_ofFn,Function.comp_def]
  rw [remaining_weights_fin_marker_bits j,
    literal_digits_of_fn_range formula.length (fun i : ℕ => if i=j.val then [true] else []),
    remaining_weights_constant_of_fn]
  simp
 theorem sat_target_positional_payloads (formula : SAT.CNF) :
    positionalDigitPayloads (fun t => satTargetDigits formula (finSumFinEquiv.symm t))=
      List.replicate formula.length (satClauseTarget formula).bits ++
        List.replicate (satVariables formula) [true] := by
  have hd : (fun t => satTargetDigits formula (finSumFinEquiv.symm t))=
      Fin.append (fun _ : Fin (satVariables formula) => (1 : ℕ))
        (fun _ : Fin formula.length => satClauseTarget formula) := by
    funext t
    refine Fin.addCases ?_ ?_ t
    · intro v;simp [satTargetDigits]
    · intro l;simp [satTargetDigits]
  simp only [positionalDigitPayloads,hd,List.ofFn_fin_append,List.reverse_append,List.map_append,
    List.map_reverse,List.map_ofFn,Function.comp_def]
  rw [remaining_weights_constant_of_fn,remaining_weights_constant_of_fn]
  simp
 theorem polynomial_sat_slack_digits_positional (bits : List Bool) (formula : SAT.CNF)
    (j : Fin formula.length) (k : Fin (satClauseTarget formula-1)) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSlackDigits (pair bits j.val.bits)=
      payloadListCode (positionalDigitPayloads
        (fun t => satWeightDigits formula (Sum.inr (j,k)) (finSumFinEquiv.symm t))) := by
  rw [polynomial_sat_slack_digits_exact bits formula j.val h,sat_slack_positional_payloads]
 theorem polynomial_sat_target_digits_positional (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATTargetDigits bits=
      payloadListCode (positionalDigitPayloads (fun t => satTargetDigits formula (finSumFinEquiv.symm t))) := by
  rw [polynomial_sat_target_digits_exact bits formula h,sat_target_positional_payloads]
 theorem polynomial_sat_slack_weight_exact (bits : List Bool) (formula : SAT.CNF)
    (j : Fin formula.length) (k : Fin (satClauseTarget formula-1)) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSlackWeight (pair bits j.val.bits)=(satSubsetWeights formula (Sum.inr (j,k))).bits := by
  simp only [polynomialSATSlackWeight,pairFst_pair,polynomial_sat_cnf_parse_exact bits formula h,
    pairSnd_pair,polynomial_sat_digit_base_exact,polynomial_sat_slack_digits_positional bits formula j k h]
  change canonicalWord (polynomialWordListHorner (actualSATWeightHornerInput formula (Sum.inr (j,k))))=_
  rw [canonical_word_eq_bits,actual_sat_weight_horner_word_value]
 theorem polynomial_sat_target_weight_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATTargetWeight bits=(satSubsetTarget formula).bits := by
  simp only [polynomialSATTargetWeight,polynomial_sat_cnf_parse_exact bits formula h,
    pairSnd_pair,polynomial_sat_digit_base_exact,polynomial_sat_target_digits_positional bits formula h]
  change canonicalWord (polynomialWordListHorner (actualSATTargetHornerInput formula))=_
  rw [canonical_word_eq_bits,actual_sat_target_horner_word_value]
 theorem sat_slack_weight_actual_polytime : polynomialSATSlackWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF) (j : Fin formula.length) (k : Fin (satClauseTarget formula-1)),
      SAT.CNF.decode? bits=some formula →
        polynomialSATSlackWeight (pair bits j.val.bits)=(satSubsetWeights formula (Sum.inr (j,k))).bits :=
  ⟨polynomial_sat_slack_weight_mem_fp,polynomial_sat_slack_weight_exact⟩
 theorem sat_target_weight_actual_polytime : polynomialSATTargetWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF), SAT.CNF.decode? bits=some formula →
      polynomialSATTargetWeight bits=(satSubsetTarget formula).bits :=
  ⟨polynomial_sat_target_weight_mem_fp,polynomial_sat_target_weight_exact⟩
#print axioms polynomial_sat_slack_weight_exact
#print axioms polynomial_sat_target_weight_exact
#print axioms sat_slack_weight_actual_polytime
#print axioms sat_target_weight_actual_polytime
end IV04.Paper.Computational
