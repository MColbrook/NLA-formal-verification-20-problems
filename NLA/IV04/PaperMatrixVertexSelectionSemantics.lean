module

public import NLA.IV04.PaperMatrixVertexSelectionPoly
public import NLA.IV04.PaperMatrixCoefficientInputSemantics
public import NLA.IV04.PaperVertexSelectionRejection
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem matrix_vertex_selection_argument_code (matrix dimension denominator tail rest choices : List Bool)
    (rows : List (List Bool × List Bool))
    (hdecoded : encodedMatrixCoefficientInput matrix=
      pair [true] (pair dimension (pair denominator (pair (endpointWordPairsCode rows rest) tail))))
    (hsize : wordValue dimension*wordValue dimension=rows.length) :
    matrixVertexSelectionArgument (pair matrix choices)=vertexSelectionInputCode rows rest choices := by
  simp only [matrixVertexSelectionArgument,matrixVertexDecoded,pairFst_pair,hdecoded,pairSnd_pair,
    canonicalWordMultiply,canonical_word_eq_bits,polynomial_word_multiply_value,hsize,vertexSelectionInputCode]

theorem matrix_vertex_selection_correct (matrix dimension denominator tail rest choices : List Bool)
    (rows : List (List Bool × List Bool))
    (hdecoded : encodedMatrixCoefficientInput matrix=
      pair [true] (pair dimension (pair denominator (pair (endpointWordPairsCode rows rest) tail))))
    (hsize : wordValue dimension*wordValue dimension=rows.length)
    (ho : endpointWordsOrdered rows) (hq : rows.length ≤ choices.length) :
    encodedMatrixVertexSelection (pair matrix choices)=
      pair [true] (pair dimension (pair denominator
        (pair (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
          (pair rest (choices.drop rows.length))) tail))) := by
  have harg := matrix_vertex_selection_argument_code matrix dimension denominator tail rest choices rows hdecoded hsize
  have hsel : encodedVertexSelection (matrixVertexSelectionArgument (pair matrix choices))=
      pair [true] (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
        (pair rest (choices.drop rows.length))) := by
    rw [harg]
    exact vertex_selection_input_codes rows rest choices ho hq
  simp only [encodedMatrixVertexSelection,hsel,matrixVertexDecoded,pairFst_pair,hdecoded,pairSnd_pair]
  rfl

theorem matrix_vertex_selection_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    pairFst (encodedMatrixVertexSelection (pair matrix choices))=[false] := by
  have hf := matrix_coefficient_input_failure matrix h
  simp only [encodedMatrixVertexSelection,pairFst_pair]
  simp only [matrixVertexDecoded,pairFst_pair,hf,andBit,caseBit₀]
  rfl

#print axioms matrix_vertex_selection_correct
end IV04.Paper.Computational
