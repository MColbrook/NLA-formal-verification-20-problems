module

public import NLA.IV04.PaperMatrixVertexDecision
public import NLA.IV04.PaperMatrixVerifierWitnessBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem verified_vertex_selection_invalid_input_flag (rows : List (List Bool × List Bool)) (rest choices : List Bool)
    (hbad : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length)) :
    pairFst (encodedVertexSelection (vertexSelectionInputCode rows rest choices))=[false] := by
  exact vertex_selection_invalid_input_flag rows rest choices hbad

theorem verified_matrix_determinant_verifier_invalid_rational_choice (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n)
    (hbad : ¬((∀ row ∈ pairs, row.1 ≤ row.2) ∧ n*n ≤ choices.length)) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=[false] := by
  exact matrix_determinant_verifier_invalid_rational_choice matrix choices tail n pairs threshold hread hsize hbad

theorem verified_matrix_determinant_verifier_all_rational_inputs (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
        rationalDenseEndpointAll n 0 0 pairs ∧ threshold ≤ (rationalEndpointVertex n pairs choices).det)] := by
  exact matrix_determinant_verifier_all_rational_inputs matrix choices tail n pairs threshold hread hsize

theorem verified_matrix_bounded_witness_actual_vertex (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : choices.length=n*n) :
    matrixBoundedWitness matrix choices ↔ tail=[] ∧ rationalDenseEndpointAll n 0 0 pairs ∧
      threshold ≤ (rationalEndpointVertex n pairs choices).det := by
  exact matrix_bounded_witness_actual_vertex matrix choices tail n pairs threshold hread hsize horder hchoices

theorem verified_matrix_verifier_actual_vertex_certificate_complete (matrix choices : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : choices.length=n*n) (hsupport : rationalDenseEndpointAll n 0 0 pairs)
    (hdet : threshold ≤ (rationalEndpointVertex n pairs choices).det) : matrix ∈ matrixVerifierLanguage := by
  exact matrix_verifier_actual_vertex_certificate_complete matrix choices n pairs threshold hread hsize horder hchoices hsupport hdet

theorem verified_matrix_verifier_language_rejects_decode_failure (matrix : List Bool)
    (hread : readMatrixRationals matrix=none) : matrix ∉ matrixVerifierLanguage := by
  exact matrix_verifier_language_rejects_decode_failure matrix hread

theorem verified_matrix_rational_decode_pair_shape (matrix : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (hread : readMatrixRationals matrix=some (n,values,tail)) :
    ∃ pairs : List (ℚ × ℚ), ∃ threshold : ℚ, pairs.length=n*n ∧
      values=pairs.flatMap (fun row => [row.1,row.2])++[threshold] := by
  exact matrix_rational_decode_pair_shape matrix n values tail hread

theorem verified_matrix_bounded_witness_all_rational_inputs (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    matrixBoundedWitness matrix choices ↔ tail=[] ∧ choices.length=n*n ∧
      (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
      threshold ≤ (rationalEndpointVertex n pairs choices).det := by
  exact matrix_bounded_witness_all_rational_inputs matrix choices tail n pairs threshold hread hsize

theorem verified_matrix_verifier_language_exact_vertex_language (matrix : List Bool) :
    matrix ∈ matrixVerifierLanguage ↔ matrix ∈ rationalMatrixVertexDecisionLanguage := by
  exact matrix_verifier_language_exact_vertex_language matrix

theorem verified_rational_matrix_vertex_decision_language_mem_np : rationalMatrixVertexDecisionLanguage ∈ NP := by
  exact rational_matrix_vertex_decision_language_mem_np

#print axioms IV04.Paper.Computational.verified_vertex_selection_invalid_input_flag
#print axioms IV04.Paper.Computational.verified_matrix_determinant_verifier_invalid_rational_choice
#print axioms IV04.Paper.Computational.verified_matrix_determinant_verifier_all_rational_inputs
#print axioms IV04.Paper.Computational.verified_matrix_bounded_witness_actual_vertex
#print axioms IV04.Paper.Computational.verified_matrix_verifier_actual_vertex_certificate_complete
#print axioms IV04.Paper.Computational.verified_matrix_verifier_language_rejects_decode_failure
#print axioms IV04.Paper.Computational.verified_matrix_rational_decode_pair_shape
#print axioms IV04.Paper.Computational.verified_matrix_bounded_witness_all_rational_inputs
#print axioms IV04.Paper.Computational.verified_matrix_verifier_language_exact_vertex_language
#print axioms IV04.Paper.Computational.verified_rational_matrix_vertex_decision_language_mem_np
end IV04.Paper.Computational
