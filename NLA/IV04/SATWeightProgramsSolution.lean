module

public import NLA.IV04.PaperSATRemainingWeightsSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
theorem verified_variable_marker_clock_length : ∀ (clock input : List Bool),
  ((variableMarkerStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+8*clock.length := variable_marker_clock_length

theorem verified_polynomial_sat_variable_markers_length : ∀ (input : List Bool),
  (polynomialSATVariableMarkers input).length ≤ 10*input.length+14 := polynomial_sat_variable_markers_length

theorem verified_polynomial_sat_variable_markers_mem_fp : polynomialSATVariableMarkers ∈ FP := polynomial_sat_variable_markers_mem_fp

theorem verified_polynomial_sat_variable_markers_exact : ∀ (ruler : List Bool) (bound v : ℕ)
    (h : bound ≤ ruler.length+1),
  polynomialSATVariableMarkers (pair ruler (pair bound.bits v.bits))=
      payloadListCode (((List.range bound).map fun i => if i=v then [true] else []).reverse) := polynomial_sat_variable_markers_exact

theorem verified_sat_variable_markers_actual_polytime : polynomialSATVariableMarkers ∈ FP ∧
    (∀ input, (polynomialSATVariableMarkers input).length ≤ 10*input.length+14) ∧
    (∀ (ruler : List Bool) (bound v : ℕ), bound ≤ ruler.length+1 →
      polynomialSATVariableMarkers (pair ruler (pair bound.bits v.bits))=
        payloadListCode (((List.range bound).map fun i => if i=v then [true] else []).reverse)) := sat_variable_markers_actual_polytime

theorem verified_polynomial_sat_literal_digits_mem_fp : polynomialSATLiteralDigits ∈ FP := polynomial_sat_literal_digits_mem_fp

theorem verified_polynomial_sat_literal_weight_mem_fp : polynomialSATLiteralWeight ∈ FP := polynomial_sat_literal_weight_mem_fp

theorem verified_polynomial_sat_literal_digits_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (v : ℕ) (b : Bool) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATLiteralDigits (pair bits (pair v.bits [b]))=
      payloadListCode (((formula.map fun clause => (literalCount clause v b).bits).reverse) ++
        (((List.range (satVariables formula)).map fun i => if i=v then [true] else []).reverse)) := polynomial_sat_literal_digits_exact

theorem verified_polynomial_sat_digit_base_exact : ∀ (formula : SAT.CNF),
  polynomialSATDigitBase (satFormulaPayload formula)=(satDigitBase formula).bits := polynomial_sat_digit_base_exact

theorem verified_polynomial_sat_literal_digits_positional : ∀ (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (b : Bool) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATLiteralDigits (pair bits (pair v.val.bits [b]))=
      payloadListCode (positionalDigitPayloads
        (fun k => satWeightDigits formula (Sum.inl (v,b)) (finSumFinEquiv.symm k))) := polynomial_sat_literal_digits_positional

theorem verified_polynomial_sat_literal_weight_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (b : Bool) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATLiteralWeight (pair bits (pair v.val.bits [b]))=
      (satSubsetWeights formula (Sum.inl (v,b))).bits := polynomial_sat_literal_weight_exact

theorem verified_sat_literal_weight_actual_polytime : polynomialSATLiteralWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF) (v : Fin (satVariables formula)) (b : Bool),
      SAT.CNF.decode? bits=some formula →
        polynomialSATLiteralWeight (pair bits (pair v.val.bits [b]))=
          (satSubsetWeights formula (Sum.inl (v,b))).bits := sat_literal_weight_actual_polytime

theorem verified_bounded_payload_repeat_clock_length : ∀ (clock input : List Bool),
  ((boundedPayloadRepeatStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+(2*input.length+8)*clock.length := bounded_payload_repeat_clock_length

theorem verified_polynomial_bounded_payload_repeat_length : ∀ (input : List Bool),
  (polynomialBoundedPayloadRepeat input).length ≤
      2*input.length+6+(2*input.length+8)*(input.length+1) := polynomial_bounded_payload_repeat_length

theorem verified_polynomial_bounded_payload_repeat_mem_fp : polynomialBoundedPayloadRepeat ∈ FP := polynomial_bounded_payload_repeat_mem_fp

theorem verified_polynomial_bounded_payload_repeat_exact : ∀ (ruler coefficient : List Bool) (bound : ℕ)
    (h : bound ≤ ruler.length+1),
  polynomialBoundedPayloadRepeat (pair ruler (pair bound.bits coefficient))=
      payloadListCode (List.replicate bound coefficient) := polynomial_bounded_payload_repeat_exact

theorem verified_bounded_payload_repeat_actual_polytime : polynomialBoundedPayloadRepeat ∈ FP ∧
    (∀ input, (polynomialBoundedPayloadRepeat input).length ≤
      2*input.length+6+(2*input.length+8)*(input.length+1)) ∧
    (∀ (ruler coefficient : List Bool) (bound : ℕ), bound ≤ ruler.length+1 →
      polynomialBoundedPayloadRepeat (pair ruler (pair bound.bits coefficient))=
        payloadListCode (List.replicate bound coefficient)) := bounded_payload_repeat_actual_polytime

theorem verified_polynomial_sat_clause_target_exact : ∀ (formula : SAT.CNF),
  polynomialSATClauseTarget (satFormulaPayload formula)=(satClauseTarget formula).bits := polynomial_sat_clause_target_exact

theorem verified_polynomial_sat_slack_digits_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (j : ℕ) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATSlackDigits (pair bits j.bits)=
      payloadListCode ((((List.range formula.length).map fun i => if i=j then [true] else []).reverse) ++
        List.replicate (satVariables formula) []) := polynomial_sat_slack_digits_exact

theorem verified_polynomial_sat_target_digits_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATTargetDigits bits=
      payloadListCode (List.replicate formula.length (satClauseTarget formula).bits ++
        List.replicate (satVariables formula) [true]) := polynomial_sat_target_digits_exact

theorem verified_polynomial_sat_slack_weight_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (j : Fin formula.length) (k : Fin (satClauseTarget formula-1)) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATSlackWeight (pair bits j.val.bits)=(satSubsetWeights formula (Sum.inr (j,k))).bits := polynomial_sat_slack_weight_exact

theorem verified_polynomial_sat_target_weight_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATTargetWeight bits=(satSubsetTarget formula).bits := polynomial_sat_target_weight_exact

theorem verified_sat_slack_weight_actual_polytime : polynomialSATSlackWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF) (j : Fin formula.length) (k : Fin (satClauseTarget formula-1)),
      SAT.CNF.decode? bits=some formula →
        polynomialSATSlackWeight (pair bits j.val.bits)=(satSubsetWeights formula (Sum.inr (j,k))).bits := sat_slack_weight_actual_polytime

theorem verified_sat_target_weight_actual_polytime : polynomialSATTargetWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF), SAT.CNF.decode? bits=some formula →
      polynomialSATTargetWeight bits=(satSubsetTarget formula).bits := sat_target_weight_actual_polytime

#print axioms IV04.Paper.Computational.verified_variable_marker_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_variable_markers_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_variable_markers_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_variable_markers_exact
#print axioms IV04.Paper.Computational.verified_sat_variable_markers_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_digits_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_weight_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_digits_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_digit_base_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_digits_positional
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_weight_exact
#print axioms IV04.Paper.Computational.verified_sat_literal_weight_actual_polytime
#print axioms IV04.Paper.Computational.verified_bounded_payload_repeat_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_repeat_length
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_repeat_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_repeat_exact
#print axioms IV04.Paper.Computational.verified_bounded_payload_repeat_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_target_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_slack_digits_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_target_digits_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_slack_weight_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_target_weight_exact
#print axioms IV04.Paper.Computational.verified_sat_slack_weight_actual_polytime
#print axioms IV04.Paper.Computational.verified_sat_target_weight_actual_polytime
end IV04.Paper.Computational
