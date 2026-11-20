module

public import NLA.IV04.PaperSATWeightTableLayout
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational
open Complexity SATReduction
theorem verified_bounded_payload_map_step_pair : ∀ (f : List Bool → List Bool)
    (index bound query output : List Bool),
  boundedPayloadMapStep f (variableMarkerPack index bound query output)=
      caseBit₀ (notBit (polynomialWordLe bound index))
        (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound query
          (f (pair query index) ++ output)) (variableMarkerPack index bound query output) := bounded_payload_map_step_pair

theorem verified_bounded_payload_map_step_shape : ∀ (f : List Bool → List Bool)
    (index bound query output : List Bool),
  ∃ i o : List Bool, boundedPayloadMapStep f (variableMarkerPack index bound query output)=
      variableMarkerPack i bound query o ∧ i.length ≤ index.length+2 ∧
      o.length ≤ output.length+2*(f (pair query index)).length+2 := bounded_payload_map_step_shape

theorem verified_bounded_payload_map_iteration_bound : ∀ (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (n k : ℕ)
    (bound query : List Bool) (hq : query.length ≤ n) (hk : k ≤ n+1),
  ∃ i o : List Bool,
      ((boundedPayloadMapStep f)^[k]) (variableMarkerPack [] bound query [])=
        variableMarkerPack i bound query o ∧
      i.length ≤ 2*k ∧ o.length ≤ (2*p.eval (4*n+4)+2)*k := bounded_payload_map_iteration_bound

theorem verified_bounded_payload_map_clock_bound : ∀ (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (input : List Bool) (k : ℕ)
    (hk : k ≤ input.length+1),
  (((boundedPayloadMapStep f)^[k])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+(2*p.eval (4*input.length+4)+6)*k := bounded_payload_map_clock_bound

theorem verified_bounded_payload_map_bound_poly : ∀ (p : Polynomial ℕ),
  PolyBound fun n => 2*n+6+(2*p.eval (4*n+4)+6)*(n+1) := bounded_payload_map_bound_poly

theorem verified_polynomial_bounded_payload_map_mem_fp : ∀ (f : List Bool → List Bool) (hf : f ∈ FP),
  polynomialBoundedPayloadMap f ∈ FP := polynomial_bounded_payload_map_mem_fp

theorem verified_bounded_payload_map_step_nat : ∀ (f : List Bool → List Bool) (i bound : ℕ)
    (query output : List Bool),
  boundedPayloadMapStep f (variableMarkerPack i.bits bound.bits query output)=
      if i<bound then variableMarkerPack (i+1).bits bound.bits query
        (f (pair query i.bits) ++ output)
      else variableMarkerPack i.bits bound.bits query output := bounded_payload_map_step_nat

theorem verified_bounded_payload_map_iterate_inactive : ∀ (f : List Bool → List Bool) (k i bound : ℕ)
    (query output : List Bool) (h : bound ≤ i),
  ((boundedPayloadMapStep f)^[k]) (variableMarkerPack i.bits bound.bits query output)=
      variableMarkerPack i.bits bound.bits query output := bounded_payload_map_iterate_inactive

theorem verified_bounded_payload_map_iteration_prefix : ∀ (f : List Bool → List Bool)
    (query : List Bool) (k bound : ℕ) (hk : k ≤ bound),
  ((boundedPayloadMapStep f)^[k]) (variableMarkerPack (0 : ℕ).bits bound.bits query [])=
      variableMarkerPack k.bits bound.bits query
        ((List.range k).reverse.flatMap (fun i => f (pair query i.bits))) := bounded_payload_map_iteration_prefix

theorem verified_polynomial_bounded_payload_map_exact : ∀ (f : List Bool → List Bool)
    (ruler query : List Bool) (bound : ℕ) (h : bound ≤ ruler.length+1),
  polynomialBoundedPayloadMap f (pair ruler (pair bound.bits query))=
      (List.range bound).reverse.flatMap (fun i => f (pair query i.bits)) := polynomial_bounded_payload_map_exact

theorem verified_polynomial_bounded_payload_map_length : ∀ (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (input : List Bool),
  (polynomialBoundedPayloadMap f input).length ≤
      2*input.length+6+(2*p.eval (4*input.length+4)+6)*(input.length+1) := polynomial_bounded_payload_map_length

theorem verified_bounded_payload_map_actual_polytime : ∀ (f : List Bool → List Bool) (hf : f ∈ FP),
  polynomialBoundedPayloadMap f ∈ FP ∧
    (∃ p : Polynomial ℕ, ∀ input, (polynomialBoundedPayloadMap f input).length ≤
      2*input.length+6+(2*p.eval (4*input.length+4)+6)*(input.length+1)) ∧
    (∀ (ruler query : List Bool) (bound : ℕ), bound ≤ ruler.length+1 →
      polynomialBoundedPayloadMap f (pair ruler (pair bound.bits query))=
        (List.range bound).reverse.flatMap (fun i => f (pair query i.bits))) := bounded_payload_map_actual_polytime

theorem verified_polynomial_sat_partition_code_mem_fp : polynomialSATPartitionCode ∈ FP := polynomial_sat_partition_code_mem_fp

theorem verified_polynomial_sat_table_metadata_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATTableMetadata bits=pair (satVariables formula).bits
      (pair formula.length.bits (satLiteralBudget formula).bits) := polynomial_sat_table_metadata_exact

theorem verified_polynomial_sat_slack_copies_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATSlackCopies bits=(satClauseTarget formula-1).bits := polynomial_sat_slack_copies_exact

theorem verified_polynomial_sat_table_count_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATTableCount bits=(satSlotCount formula).bits := polynomial_sat_table_count_exact

theorem verified_polynomial_sat_literal_chunk_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATLiteralChunk (pair bits v.val.bits)=
      payloadListCode (List.ofFn (fun b : Fin 2 =>
        (satSubsetWeights formula (Sum.inl (v,boolFinTwo.symm b))).bits)).reverse := polynomial_sat_literal_chunk_exact

theorem verified_polynomial_sat_slack_chunk_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (j : Fin formula.length) (h : SAT.CNF.decode? bits=some formula),
  polynomialSATSlackChunk (pair bits j.val.bits)=
      payloadListCode (List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
        (satSubsetWeights formula (Sum.inr (j,k))).bits)).reverse := polynomial_sat_slack_chunk_exact

theorem verified_sat_table_subset_layout : ∀ (formula : SAT.CNF),
  List.ofFn (fun i : Fin (satSlotCount formula) =>
      (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)=
      (List.ofFn (fun v : Fin (satVariables formula) => List.ofFn (fun b : Fin 2 =>
        (satSubsetWeights formula (Sum.inl (v,boolFinTwo.symm b))).bits))).flatten ++
      (List.ofFn (fun j : Fin formula.length => List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
        (satSubsetWeights formula (Sum.inr (j,k))).bits))).flatten := sat_table_subset_layout

theorem verified_polynomial_sat_reversed_weights_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATReversedWeights bits=payloadListCode
      (List.ofFn (fun i : Fin (satSlotCount formula) =>
        (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)).reverse := polynomial_sat_reversed_weights_exact

theorem verified_polynomial_sat_weight_table_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATWeightTable bits=payloadListCode
      (List.ofFn (fun i : Fin (satSlotCount formula) =>
        (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)) := polynomial_sat_weight_table_exact

theorem verified_polynomial_sat_subset_input_exact : ∀ (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula),
  polynomialSATSubsetInput bits=subsetPartitionBuilderInput (satSlotCount formula)
      (fun i => satSubsetWeights formula ((satSlotFinEquiv formula).symm i)) (satSubsetTarget formula) := polynomial_sat_subset_input_exact

theorem verified_sat_table_builder_weights_exact : ∀ (formula : SAT.CNF),
  subsetPartitionBuilderWeights
      (fun i : Fin (satSlotCount formula) => satSubsetWeights formula ((satSlotFinEquiv formula).symm i))
      (satSubsetTarget formula)=satPartitionWeight formula := sat_table_builder_weights_exact

theorem verified_polynomial_sat_partition_code_exact : ∀ (bits : List Bool),
  polynomialSATPartitionCode bits=binarySATPartitionReduction bits := polynomial_sat_partition_code_exact

theorem verified_sat_partition_code_actual_polytime : polynomialSATPartitionCode ∈ FP ∧
    (∀ bits, polynomialSATPartitionCode bits=binarySATPartitionReduction bits) ∧
    (∀ bits, bits ∈ Complexity.SAT.language ↔
      polynomialSATPartitionCode bits ∈ positivePartitionLanguage) := sat_partition_code_actual_polytime

#print axioms IV04.Paper.Computational.verified_bounded_payload_map_step_pair
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_step_shape
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_iteration_bound
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_clock_bound
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_bound_poly
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_map_mem_fp
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_step_nat
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_iterate_inactive
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_iteration_prefix
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_map_exact
#print axioms IV04.Paper.Computational.verified_polynomial_bounded_payload_map_length
#print axioms IV04.Paper.Computational.verified_bounded_payload_map_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_sat_partition_code_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_table_metadata_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_slack_copies_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_table_count_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_literal_chunk_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_slack_chunk_exact
#print axioms IV04.Paper.Computational.verified_sat_table_subset_layout
#print axioms IV04.Paper.Computational.verified_polynomial_sat_reversed_weights_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_weight_table_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_subset_input_exact
#print axioms IV04.Paper.Computational.verified_sat_table_builder_weights_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_partition_code_exact
#print axioms IV04.Paper.Computational.verified_sat_partition_code_actual_polytime
end IV04.Paper.Computational
