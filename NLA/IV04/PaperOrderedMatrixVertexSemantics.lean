module

public import NLA.IV04.PaperOrderedMatrixVertexPoly
public import NLA.IV04.PaperPayloadReverseSemantics
public import NLA.IV04.PaperMatrixVertexSelectionRational
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem order_matrix_vertex_output_flag (selected : List Bool) :
    pairFst (orderMatrixVertexOutput selected)=pairFst selected := by
  simp only [orderMatrixVertexOutput,pairFst_pair]

theorem order_matrix_vertex_output_code (flag dimension denominator fields choices tail : List Bool)
    (words : List (List Bool)) :
    orderMatrixVertexOutput
      (pair flag (pair dimension (pair denominator
        (pair (pair (payloadListCode words.reverse) (pair fields choices)) tail))))=
      pair flag (pair dimension (pair denominator
        (pair (pair (payloadListCode words) (pair fields choices)) tail))) := by
  simp only [orderMatrixVertexOutput,pairFst_pair,pairSnd_pair,payload_reverse_code,List.reverse_reverse]

theorem ordered_matrix_vertex_selection_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    pairFst (encodedOrderedMatrixVertexSelection (pair matrix choices))=[false] := by
  rw [encodedOrderedMatrixVertexSelection,order_matrix_vertex_output_flag]
  exact matrix_vertex_selection_decode_failure matrix choices h

theorem ordered_matrix_vertex_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
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
  obtain ⟨dimension,denominator,rows,thresholdWord,hd,hD,hl,hrows,hthreshold,hout⟩ :=
    matrix_vertex_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices
  refine ⟨dimension,denominator,rows,thresholdWord,hd,hD,hl,hrows,hthreshold,?_⟩
  rw [encodedOrderedMatrixVertexSelection,hout,order_matrix_vertex_output_code]

#print axioms ordered_matrix_vertex_selection_rational_input
end IV04.Paper.Computational
