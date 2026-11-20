module

public import NLA.IV04.PaperRationalEndpointVertex
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

/-- The complete verifier compares the determinant of the literal selected endpoint matrix. -/
theorem matrix_determinant_verifier_actual_vertex_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1≤row.2)
    (hchoices : n*n≤choices.length) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n ∧ rationalDenseEndpointAll n 0 0 pairs ∧
        threshold≤(rationalEndpointVertex n pairs choices).det)] := by
  obtain ⟨dimension,denominator,rows,tword,hd,hD,hrsize,hrows,hT,hout⟩ :=
    matrix_determinant_verifier_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices
  by_cases hsupport : rationalDenseEndpointAll n 0 0 pairs
  · have he := dense_word_selected_rational_matrix n (wordValue denominator) rows pairs choices hD hrows
    have htri : RationalTridiagonal (denseWordRationalMatrix n (wordValue denominator) (selectedEndpointWords rows choices)) := by
      rw [he]
      exact rational_endpoint_vertex_tridiagonal n pairs choices hsupport
    have hc := (dense_word_matrix_equals_continuant n (wordValue denominator) (selectedEndpointWords rows choices) htri).symm.trans he
    rw [hc] at hout
    exact hout
  · simpa [hsupport] using hout

#print axioms matrix_determinant_verifier_actual_vertex_input
end IV04.Paper.Computational