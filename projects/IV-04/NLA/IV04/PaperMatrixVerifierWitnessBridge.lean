module

public import NLA.IV04.PaperMatrixVerifierActualVertex
public import NLA.IV04.PaperMatrixVerifierNP
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem matrix_bounded_witness_actual_vertex (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : choices.length=n*n) :
    matrixBoundedWitness matrix choices ↔ tail=[] ∧ rationalDenseEndpointAll n 0 0 pairs ∧
      threshold ≤ (rationalEndpointVertex n pairs choices).det := by
  have hb := matrix_vertex_certificate_bit_budget matrix n _ tail hread
  have hbudget : n*n ≤ matrix.length+1 := by omega
  have hout := matrix_determinant_verifier_actual_vertex_input matrix choices tail n pairs threshold
    hread hsize horder (by rw [hchoices])
  rw [matrixBoundedWitness,hout]
  simp [hbudget,hchoices]

theorem matrix_verifier_actual_vertex_certificate_complete (matrix choices : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : choices.length=n*n) (hsupport : rationalDenseEndpointAll n 0 0 pairs)
    (hdet : threshold ≤ (rationalEndpointVertex n pairs choices).det) : matrix ∈ matrixVerifierLanguage := by
  exact ⟨choices,(matrix_bounded_witness_actual_vertex matrix choices [] n pairs threshold
    hread hsize horder hchoices).mpr ⟨rfl,hsupport,hdet⟩⟩

theorem matrix_verifier_language_rejects_decode_failure (matrix : List Bool)
    (hread : readMatrixRationals matrix=none) : matrix ∉ matrixVerifierLanguage := by
  rintro ⟨choices,_,haccept⟩
  rw [matrix_determinant_verifier_decode_failure matrix choices hread] at haccept
  contradiction

#print axioms matrix_bounded_witness_actual_vertex
end IV04.Paper.Computational