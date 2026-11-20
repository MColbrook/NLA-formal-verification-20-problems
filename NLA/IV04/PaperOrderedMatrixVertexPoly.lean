module

public import NLA.IV04.PaperOrderedMatrixVertexDefinitions
public import NLA.IV04.PaperMatrixVertexSelectionPoly
public import NLA.IV04.PaperPayloadReversePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

set_option maxHeartbeats 2000000 in
theorem order_matrix_vertex_output_cobham :
    Cobham fun v : Fin 1 → List Bool => orderMatrixVertexOutput (v 0) := by
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn
    (Cobham.proj (0 : Fin 1)))))
  have hw := unary_input_cobham_comp polynomial_payload_reverse_cobham (Cobham.fstBlockFn hb)
  have ho := input_pair_cobham_comp hw (Cobham.sndBlockFn hb)
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn
    (Cobham.proj (0 : Fin 1)))))
  have hD := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hd := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hf := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  simpa only [orderMatrixVertexOutput] using
    input_pair_cobham_comp hf (input_pair_cobham_comp hd
      (input_pair_cobham_comp hD (input_pair_cobham_comp ho ht)))

theorem encoded_ordered_matrix_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedOrderedMatrixVertexSelection (v 0) := by
  simpa only [encodedOrderedMatrixVertexSelection] using
    unary_input_cobham_comp order_matrix_vertex_output_cobham encoded_matrix_vertex_selection_cobham

theorem encoded_ordered_matrix_vertex_selection_mem_fp : encodedOrderedMatrixVertexSelection ∈ FP :=
  CobhamFP_subset_FP encoded_ordered_matrix_vertex_selection_cobham

#print axioms encoded_ordered_matrix_vertex_selection_mem_fp
end IV04.Paper.Computational
