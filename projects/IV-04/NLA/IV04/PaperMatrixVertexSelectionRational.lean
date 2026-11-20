module

public import NLA.IV04.PaperMatrixVertexSelectionBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem matrix_vertex_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
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
  obtain ⟨dimension,denominator,coefficients,hdecoded,hdim,hD,hvalues,_⟩ :=
    matrix_coefficient_input_correct matrix n _ tail hread
  obtain ⟨rows,tword,hcoefficients,hrows,hthreshold⟩ :=
    scaled_endpoint_words_split pairs threshold (wordValue denominator) coefficients hvalues
  have hlen : rows.length=pairs.length := by
    have h := congrArg List.length hrows
    simpa only [List.length_map] using h
  have hrsize : rows.length=n*n := hlen.trans hsize
  have htable : payloadListCode coefficients=endpointWordPairsCode rows (payloadListCode [tword]) := by
    rw [endpoint_word_pairs_code_flatten,hcoefficients]
  rw [htable] at hdecoded
  have ho : endpointWordsOrdered rows :=
    scaled_endpoint_words_ordered pairs rows (wordValue denominator) hD hrows horder
  have hc : wordValue dimension*wordValue dimension=rows.length := by rw [hdim,hrsize]
  have hq : rows.length ≤ choices.length := by rw [hrsize]; exact hchoices
  have hout := matrix_vertex_selection_correct matrix dimension denominator tail (payloadListCode [tword])
    choices rows hdecoded hc ho hq
  rw [hrsize] at hout
  exact ⟨dimension,denominator,rows,tword,hdim,hD,hrsize,hrows,hthreshold,hout⟩

#print axioms matrix_vertex_selection_rational_input
end IV04.Paper.Computational
