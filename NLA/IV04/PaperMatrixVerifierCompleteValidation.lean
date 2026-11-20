module

public import NLA.IV04.PaperVertexSelectionCompleteValidation
public import NLA.IV04.PaperMatrixVerifierActualVertex
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem scaled_endpoint_words_ordered_iff (pairs : List (ℚ × ℚ)) (rows : List (List Bool × List Bool))
    (D : ℕ) (hD : 0<D)
    (hmap : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    endpointWordsOrdered rows ↔ ∀ row ∈ pairs, row.1 ≤ row.2 := by
  refine ⟨?_,scaled_endpoint_words_ordered pairs rows D hD hmap⟩
  intro ho p hp
  have hm : (p.1*(D : ℚ),p.2*(D : ℚ)) ∈ rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ))) := by
    rw [hmap];exact List.mem_map.mpr ⟨p,hp,rfl⟩
  obtain ⟨row,hr,he⟩ := List.mem_map.mp hm
  have hl : (signedWordValue row.1 : ℚ) ≤ (signedWordValue row.2 : ℚ) := by exact_mod_cast ho row hr
  have hlower : (signedWordValue row.1 : ℚ)=p.1*(D : ℚ) := congrArg Prod.fst he
  have hupper : (signedWordValue row.2 : ℚ)=p.2*(D : ℚ) := congrArg Prod.snd he
  rw [hlower,hupper] at hl
  exact le_of_mul_le_mul_right hl (show (0 : ℚ)<D by exact_mod_cast hD)

theorem matrix_vertex_selection_invalid_flag (matrix dimension denominator tail rest choices : List Bool)
    (rows : List (List Bool × List Bool))
    (hdecoded : encodedMatrixCoefficientInput matrix=
      pair [true] (pair dimension (pair denominator (pair (endpointWordPairsCode rows rest) tail))))
    (hsize : wordValue dimension*wordValue dimension=rows.length)
    (hbad : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length)) :
    pairFst (encodedMatrixVertexSelection (pair matrix choices))=[false] := by
  have ha := matrix_vertex_selection_argument_code matrix dimension denominator tail rest choices rows hdecoded hsize
  have hf : pairFst (encodedVertexSelection (matrixVertexSelectionArgument (pair matrix choices)))=[false] := by
    rw [ha];exact vertex_selection_invalid_input_flag rows rest choices hbad
  simp only [encodedMatrixVertexSelection,pairFst_pair,hf]
  have hz (flag : List Bool) : andBit flag [false]=[false] := by
    cases flag with
    | nil => rfl
    | cons b bits => cases b <;> rfl
  exact hz _

theorem strict_matrix_selection_rejects_false_flag (selected : List Bool)
    (hflag : pairFst selected=[false]) : strictMatrixSelectionFlag selected=[false] := by
  rw [strictMatrixSelectionFlag,hflag]
  rfl

theorem matrix_verifier_rejects_strict_false (input : List Bool)
    (hstrict : encodedStrictMatrixSelectionFlag input=[false]) : encodedMatrixDeterminantVerifier input=[false] := by
  rw [encodedMatrixDeterminantVerifier,hstrict]
  rfl

theorem matrix_determinant_verifier_invalid_rational_choice (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n)
    (hbad : ¬((∀ row ∈ pairs, row.1 ≤ row.2) ∧ n*n ≤ choices.length)) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=[false] := by
  obtain ⟨dimension,denominator,coefficients,hdecoded,hdim,hD,hvalues,_⟩ :=
    matrix_coefficient_input_correct matrix n _ tail hread
  obtain ⟨rows,tword,hcoefficients,hrows,hthreshold⟩ :=
    scaled_endpoint_words_split pairs threshold (wordValue denominator) coefficients hvalues
  have hlen : rows.length=pairs.length := by
    have h := congrArg List.length hrows;simpa only [List.length_map] using h
  have hrsize : rows.length=n*n := hlen.trans hsize
  have htable : payloadListCode coefficients=endpointWordPairsCode rows (payloadListCode [tword]) := by
    rw [endpoint_word_pairs_code_flatten,hcoefficients]
  rw [htable] at hdecoded
  have hc : wordValue dimension*wordValue dimension=rows.length := by rw [hdim,hrsize]
  have hb : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length) := by
    rintro ⟨ho,hq⟩;apply hbad
    exact ⟨(scaled_endpoint_words_ordered_iff pairs rows (wordValue denominator) hD hrows).mp ho,by rwa [hrsize] at hq⟩
  have hflag := matrix_vertex_selection_invalid_flag matrix dimension denominator tail (payloadListCode [tword]) choices rows hdecoded hc hb
  have hordered : pairFst (encodedOrderedMatrixVertexSelection (pair matrix choices))=[false] :=
    (order_matrix_vertex_output_flag (encodedMatrixVertexSelection (pair matrix choices))).trans hflag
  have hstrict : encodedStrictMatrixSelectionFlag (pair matrix choices)=[false] :=
    strict_matrix_selection_rejects_false_flag (encodedOrderedMatrixVertexSelection (pair matrix choices)) hordered
  exact matrix_verifier_rejects_strict_false (pair matrix choices) hstrict

theorem matrix_determinant_verifier_all_rational_inputs (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
        rationalDenseEndpointAll n 0 0 pairs ∧ threshold ≤ (rationalEndpointVertex n pairs choices).det)] := by
  by_cases hgood : (∀ row ∈ pairs, row.1 ≤ row.2) ∧ n*n ≤ choices.length
  · have h := matrix_determinant_verifier_actual_vertex_input matrix choices tail n pairs threshold hread hsize hgood.1 hgood.2
    have ho : (∀ row ∈ pairs, row.1 ≤ row.2) ↔ True := iff_true_intro hgood.1
    simpa only [ho,true_and] using h
  · have hfalse : ¬(tail=[] ∧ choices.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
        rationalDenseEndpointAll n 0 0 pairs ∧ threshold ≤ (rationalEndpointVertex n pairs choices).det) := by
      rintro ⟨_,hlen,ho,_,_⟩;exact hgood ⟨ho,by rw [hlen]⟩
    rw [matrix_determinant_verifier_invalid_rational_choice matrix choices tail n pairs threshold hread hsize hgood]
    simp only [hfalse,decide_false]

#print axioms matrix_determinant_verifier_all_rational_inputs
end IV04.Paper.Computational