module

public import NLA.IV04.PaperOrderedMatrixVertexSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_payload_reverse_step_pair (rest output : List Bool) :
    payloadReverseStep (Complexity.pair rest output)=
      if rest=[] then Complexity.pair rest output else Complexity.pair (Complexity.pairSnd rest)
        (Complexity.pair (Complexity.pairFst rest) output) := by
  exact payload_reverse_step_pair rest output

theorem verified_payload_reverse_step_shape (rest output : List Bool) :
    ∃ r o : List Bool, payloadReverseStep (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2 := by
  exact payload_reverse_step_shape rest output

theorem verified_payload_reverse_iterate_shape (k : ℕ) (rest output : List Bool) :
    ∃ r o : List Bool, (payloadReverseStep^[k]) (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2*k := by
  exact payload_reverse_iterate_shape k rest output

theorem verified_payload_reverse_iterate_length (k : ℕ) (rest output : List Bool) :
    ((payloadReverseStep^[k]) (Complexity.pair rest output)).length ≤
      2*rest.length+output.length+2+2*k := by
  exact payload_reverse_iterate_length k rest output

theorem verified_payload_reverse_output_length (input : List Bool) :
    (polynomialPayloadReverse input).length ≤ 4*input.length+2 := by
  exact payload_reverse_output_length input

theorem verified_payload_reverse_step_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadReverseStep (v 0) := by
  exact payload_reverse_step_cobham

theorem verified_payload_reverse_state_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadReverseState (v 0) := by
  exact payload_reverse_state_cobham

theorem verified_polynomial_payload_reverse_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPayloadReverse (v 0) := by
  exact polynomial_payload_reverse_cobham

theorem verified_polynomial_payload_reverse_mem_fp : polynomialPayloadReverse ∈ FP := by
  exact polynomial_payload_reverse_mem_fp

theorem verified_payload_reverse_iterate_nil (k : ℕ) (output : List Bool) :
    (payloadReverseStep^[k]) (pair [] output)=pair [] output := by
  exact payload_reverse_iterate_nil k output

theorem verified_payload_reverse_iterate_code (k : ℕ) (payloads output : List (List Bool))
    (h : payloads.length ≤ k) :
    (payloadReverseStep^[k]) (pair (payloadListCode payloads) (payloadListCode output))=
      pair [] (payloadListCode (payloads.reverse ++ output)) := by
  exact payload_reverse_iterate_code k payloads output h

theorem verified_payload_reverse_code (payloads : List (List Bool)) :
    polynomialPayloadReverse (payloadListCode payloads)=
      payloadListCode (payloads.reverse) := by
  exact payload_reverse_code payloads

theorem verified_payload_reverse_involution_code (payloads : List (List Bool)) :
    polynomialPayloadReverse (polynomialPayloadReverse (payloadListCode payloads))=
      payloadListCode payloads := by
  exact payload_reverse_involution_code payloads

theorem verified_payload_reverse_actual_polytime : polynomialPayloadReverse ∈ FP ∧
    (∀ input, (polynomialPayloadReverse input).length ≤ 4*input.length+2) ∧
    (∀ payloads, polynomialPayloadReverse (payloadListCode payloads)=
      payloadListCode payloads.reverse) := by
  exact payload_reverse_actual_polytime

theorem verified_order_matrix_vertex_output_cobham :
    Cobham fun v : Fin 1 → List Bool => orderMatrixVertexOutput (v 0) := by
  exact order_matrix_vertex_output_cobham

theorem verified_encoded_ordered_matrix_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedOrderedMatrixVertexSelection (v 0) := by
  exact encoded_ordered_matrix_vertex_selection_cobham

theorem verified_encoded_ordered_matrix_vertex_selection_mem_fp : encodedOrderedMatrixVertexSelection ∈ FP := by
  exact encoded_ordered_matrix_vertex_selection_mem_fp

theorem verified_order_matrix_vertex_output_flag (selected : List Bool) :
    pairFst (orderMatrixVertexOutput selected)=pairFst selected := by
  exact order_matrix_vertex_output_flag selected

theorem verified_order_matrix_vertex_output_code (flag dimension denominator fields choices tail : List Bool)
    (words : List (List Bool)) :
    orderMatrixVertexOutput
      (pair flag (pair dimension (pair denominator
        (pair (pair (payloadListCode words.reverse) (pair fields choices)) tail))))=
      pair flag (pair dimension (pair denominator
        (pair (pair (payloadListCode words) (pair fields choices)) tail))) := by
  exact order_matrix_vertex_output_code flag dimension denominator fields choices tail words

theorem verified_ordered_matrix_vertex_selection_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    pairFst (encodedOrderedMatrixVertexSelection (pair matrix choices))=[false] := by
  exact ordered_matrix_vertex_selection_decode_failure matrix choices h

theorem verified_ordered_matrix_vertex_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : n*n ≤ choices.length) :
    ∃ dimension denominator : List Bool, ∃ rows : List (List Bool × List Bool), ∃ thresholdWord : List Bool,
      wordValue dimension=n ∧ 0 < wordValue denominator ∧ rows.length=n*n ∧
      rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
        pairs.map (fun row => (row.1*(wordValue denominator : ℚ),row.2*(wordValue denominator : ℚ))) ∧
      (signedWordValue thresholdWord : ℚ)=threshold*(wordValue denominator : ℚ) ∧
      encodedOrderedMatrixVertexSelection (pair matrix choices)=
        pair [true] (pair dimension (pair denominator
          (pair (pair (payloadListCode (selectedEndpointWords rows choices))
            (pair (payloadListCode [thresholdWord]) (choices.drop (n*n)))) tail))) := by
  exact ordered_matrix_vertex_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices

#print axioms IV04.Paper.Computational.verified_payload_reverse_step_pair
#print axioms IV04.Paper.Computational.verified_payload_reverse_step_shape
#print axioms IV04.Paper.Computational.verified_payload_reverse_iterate_shape
#print axioms IV04.Paper.Computational.verified_payload_reverse_iterate_length
#print axioms IV04.Paper.Computational.verified_payload_reverse_output_length
#print axioms IV04.Paper.Computational.verified_payload_reverse_step_cobham
#print axioms IV04.Paper.Computational.verified_payload_reverse_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_payload_reverse_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_payload_reverse_mem_fp
#print axioms IV04.Paper.Computational.verified_payload_reverse_iterate_nil
#print axioms IV04.Paper.Computational.verified_payload_reverse_iterate_code
#print axioms IV04.Paper.Computational.verified_payload_reverse_code
#print axioms IV04.Paper.Computational.verified_payload_reverse_involution_code
#print axioms IV04.Paper.Computational.verified_payload_reverse_actual_polytime
#print axioms IV04.Paper.Computational.verified_order_matrix_vertex_output_cobham
#print axioms IV04.Paper.Computational.verified_encoded_ordered_matrix_vertex_selection_cobham
#print axioms IV04.Paper.Computational.verified_encoded_ordered_matrix_vertex_selection_mem_fp
#print axioms IV04.Paper.Computational.verified_order_matrix_vertex_output_flag
#print axioms IV04.Paper.Computational.verified_order_matrix_vertex_output_code
#print axioms IV04.Paper.Computational.verified_ordered_matrix_vertex_selection_decode_failure
#print axioms IV04.Paper.Computational.verified_ordered_matrix_vertex_selection_rational_input
end IV04.Paper.Computational
