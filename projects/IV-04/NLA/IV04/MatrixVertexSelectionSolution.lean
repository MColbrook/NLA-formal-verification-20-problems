module

public import NLA.IV04.PaperMatrixVertexSelectionRational
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_matrix_vertex_decoded_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixVertexDecoded (v 0) := by
  exact matrix_vertex_decoded_cobham

theorem verified_matrix_vertex_selection_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixVertexSelectionArgument (v 0) := by
  exact matrix_vertex_selection_argument_cobham

theorem verified_encoded_matrix_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixVertexSelection (v 0) := by
  exact encoded_matrix_vertex_selection_cobham

theorem verified_encoded_matrix_vertex_selection_mem_fp : encodedMatrixVertexSelection ∈ FP := by
  exact encoded_matrix_vertex_selection_mem_fp

theorem verified_matrix_vertex_selection_argument_code (matrix dimension denominator tail rest choices : List Bool)
    (rows : List (List Bool × List Bool))
    (hdecoded : encodedMatrixCoefficientInput matrix=
      pair [true] (pair dimension (pair denominator (pair (endpointWordPairsCode rows rest) tail))))
    (hsize : wordValue dimension*wordValue dimension=rows.length) :
    matrixVertexSelectionArgument (pair matrix choices)=vertexSelectionInputCode rows rest choices := by
  exact matrix_vertex_selection_argument_code matrix dimension denominator tail rest choices rows hdecoded hsize

theorem verified_matrix_vertex_selection_correct (matrix dimension denominator tail rest choices : List Bool)
    (rows : List (List Bool × List Bool))
    (hdecoded : encodedMatrixCoefficientInput matrix=
      pair [true] (pair dimension (pair denominator (pair (endpointWordPairsCode rows rest) tail))))
    (hsize : wordValue dimension*wordValue dimension=rows.length)
    (ho : endpointWordsOrdered rows) (hq : rows.length ≤ choices.length) :
    encodedMatrixVertexSelection (pair matrix choices)=
      pair [true] (pair dimension (pair denominator
        (pair (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
          (pair rest (choices.drop rows.length))) tail))) := by
  exact matrix_vertex_selection_correct matrix dimension denominator tail rest choices rows hdecoded hsize ho hq

theorem verified_matrix_vertex_selection_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    pairFst (encodedMatrixVertexSelection (pair matrix choices))=[false] := by
  exact matrix_vertex_selection_decode_failure matrix choices h

theorem verified_endpoint_word_pairs_code_flatten (rows : List (List Bool × List Bool)) (rest : List (List Bool)) :
    endpointWordPairsCode rows (payloadListCode rest)=
      payloadListCode (rows.flatMap (fun row => [row.1,row.2])++rest) := by
  exact endpoint_word_pairs_code_flatten rows rest

theorem verified_scaled_endpoint_words_split (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (denominator : ℕ) (coefficients : List (List Bool))
    (h : coefficients.map (fun word => (signedWordValue word : ℚ))=
      (pairs.flatMap (fun row => [row.1,row.2])++[threshold]).map
        (fun q => q*(denominator : ℚ))) :
    ∃ rows : List (List Bool × List Bool), ∃ thresholdWord : List Bool,
      coefficients=rows.flatMap (fun row => [row.1,row.2])++[thresholdWord] ∧
      rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
        pairs.map (fun row => (row.1*(denominator : ℚ),row.2*(denominator : ℚ))) ∧
      (signedWordValue thresholdWord : ℚ)=threshold*(denominator : ℚ) := by
  exact scaled_endpoint_words_split pairs threshold denominator coefficients h

theorem verified_scaled_endpoint_words_ordered (pairs : List (ℚ × ℚ)) (rows : List (List Bool × List Bool))
    (denominator : ℕ) (hD : 0 < denominator)
    (hmap : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(denominator : ℚ),row.2*(denominator : ℚ))))
    (ho : ∀ row ∈ pairs, row.1 ≤ row.2) : endpointWordsOrdered rows := by
  exact scaled_endpoint_words_ordered pairs rows denominator hD hmap ho

theorem verified_matrix_vertex_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
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
      encodedMatrixVertexSelection (pair matrix choices)=
        pair [true] (pair dimension (pair denominator
          (pair (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
            (pair (payloadListCode [thresholdWord]) (choices.drop (n*n)))) tail))) := by
  exact matrix_vertex_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices

#print axioms IV04.Paper.Computational.verified_matrix_vertex_decoded_cobham
#print axioms IV04.Paper.Computational.verified_matrix_vertex_selection_argument_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_vertex_selection_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_vertex_selection_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_vertex_selection_argument_code
#print axioms IV04.Paper.Computational.verified_matrix_vertex_selection_correct
#print axioms IV04.Paper.Computational.verified_matrix_vertex_selection_decode_failure
#print axioms IV04.Paper.Computational.verified_endpoint_word_pairs_code_flatten
#print axioms IV04.Paper.Computational.verified_scaled_endpoint_words_split
#print axioms IV04.Paper.Computational.verified_scaled_endpoint_words_ordered
#print axioms IV04.Paper.Computational.verified_matrix_vertex_selection_rational_input
end IV04.Paper.Computational
