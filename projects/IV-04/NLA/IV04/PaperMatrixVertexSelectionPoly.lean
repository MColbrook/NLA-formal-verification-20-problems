module

public import NLA.IV04.PaperMatrixVertexSelectionDefinitions
public import NLA.IV04.PaperMatrixCoefficientInputPoly
public import NLA.IV04.PaperVertexSelectionPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem matrix_vertex_decoded_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixVertexDecoded (v 0) := by
  simpa only [matrixVertexDecoded] using
    unary_input_cobham_comp encoded_matrix_coefficient_input_cobham
      (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1)))

theorem matrix_vertex_selection_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixVertexSelectionArgument (v 0) := by
  have hd : Cobham fun v : Fin 1 → List Bool => pairFst (pairSnd (matrixVertexDecoded (v 0))) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn matrix_vertex_decoded_cobham)
  have hf : Cobham fun v : Fin 1 → List Bool =>
      pairFst (pairSnd (pairSnd (pairSnd (matrixVertexDecoded (v 0))))) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn matrix_vertex_decoded_cobham)))
  have hn : Cobham fun v : Fin 1 → List Bool =>
      canonicalWordMultiply (pairFst (pairSnd (matrixVertexDecoded (v 0))))
        (pairFst (pairSnd (matrixVertexDecoded (v 0)))) :=
    (Cobham.comp₂ canonical_word_multiply_cobham hd hd).of_eq fun _ => rfl
  simpa only [matrixVertexSelectionArgument] using
    input_pair_cobham_comp hn (input_pair_cobham_comp hf (Cobham.sndBlockFn (.proj 0)))

set_option maxHeartbeats 2000000 in
theorem encoded_matrix_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixVertexSelection (v 0) := by
  have hs : Cobham fun v : Fin 1 → List Bool =>
      encodedVertexSelection (matrixVertexSelectionArgument (v 0)) :=
    unary_input_cobham_comp encoded_vertex_selection_cobham matrix_vertex_selection_argument_cobham
  have hf : Cobham fun v : Fin 1 → List Bool =>
      andBit (pairFst (matrixVertexDecoded (v 0)))
        (pairFst (encodedVertexSelection (matrixVertexSelectionArgument (v 0)))) :=
    Cobham.andFn (Cobham.fstBlockFn matrix_vertex_decoded_cobham) (Cobham.fstBlockFn hs)
  have hd : Cobham fun v : Fin 1 → List Bool => pairFst (pairSnd (matrixVertexDecoded (v 0))) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn matrix_vertex_decoded_cobham)
  have hD : Cobham fun v : Fin 1 → List Bool => pairFst (pairSnd (pairSnd (matrixVertexDecoded (v 0)))) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn matrix_vertex_decoded_cobham))
  have ht : Cobham fun v : Fin 1 → List Bool =>
      pairSnd (pairSnd (pairSnd (pairSnd (matrixVertexDecoded (v 0))))) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn matrix_vertex_decoded_cobham)))
  have hr := input_pair_cobham_comp hd
    (input_pair_cobham_comp hD (input_pair_cobham_comp (Cobham.sndBlockFn hs) ht))
  simpa only [encodedMatrixVertexSelection] using input_pair_cobham_comp hf hr

theorem encoded_matrix_vertex_selection_mem_fp : encodedMatrixVertexSelection ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_vertex_selection_cobham

#print axioms encoded_matrix_vertex_selection_mem_fp
end IV04.Paper.Computational
