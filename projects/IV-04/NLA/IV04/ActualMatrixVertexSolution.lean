module

public import NLA.IV04.PaperMatrixVerifierActualVertex
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem verified_selected_endpoint_words_scaled (D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    (selectedEndpointWords rows choices).map (fun word => (signedWordValue word : ℚ))=
      (selectedRationalEndpoints pairs choices).map (fun value => value*(D : ℚ)) := by
  exact selected_endpoint_words_scaled D rows pairs choices hrows

theorem verified_dense_word_selected_rational_matrix (n D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (choices : List Bool) (hD : 0<D)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    denseWordRationalMatrix n D (selectedEndpointWords rows choices)=rationalEndpointVertex n pairs choices := by
  exact dense_word_selected_rational_matrix n D rows pairs choices hD hrows

theorem verified_rational_endpoint_vertex_tridiagonal (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (hAll : rationalDenseEndpointAll n 0 0 pairs) : RationalTridiagonal (rationalEndpointVertex n pairs choices) := by
  exact rational_endpoint_vertex_tridiagonal n pairs choices hAll

theorem verified_selected_rational_endpoints_getD (pairs : List (ℚ × ℚ)) (choices : List Bool) (k : ℕ) :
    (selectedRationalEndpoints pairs choices).getD k 0=
      if choices.getD k false then (pairs.getD k (0,0)).2 else (pairs.getD k (0,0)).1 := by
  exact selected_rational_endpoints_getD pairs choices k

theorem verified_rational_endpoint_vertex_bounds (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) (i j : Fin n) :
    (pairs.getD (i.val*n+j.val) (0,0)).1 ≤ rationalEndpointVertex n pairs choices i j ∧
      rationalEndpointVertex n pairs choices i j ≤ (pairs.getD (i.val*n+j.val) (0,0)).2 := by
  exact rational_endpoint_vertex_bounds n pairs choices horder i j

theorem verified_matrix_determinant_verifier_actual_vertex_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1≤row.2)
    (hchoices : n*n≤choices.length) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n ∧ rationalDenseEndpointAll n 0 0 pairs ∧
        threshold≤(rationalEndpointVertex n pairs choices).det)] := by
  exact matrix_determinant_verifier_actual_vertex_input matrix choices tail n pairs threshold hread hsize horder hchoices

#print axioms IV04.Paper.Computational.verified_selected_endpoint_words_scaled
#print axioms IV04.Paper.Computational.verified_dense_word_selected_rational_matrix
#print axioms IV04.Paper.Computational.verified_rational_endpoint_vertex_tridiagonal
#print axioms IV04.Paper.Computational.verified_selected_rational_endpoints_getD
#print axioms IV04.Paper.Computational.verified_rational_endpoint_vertex_bounds
#print axioms IV04.Paper.Computational.verified_matrix_determinant_verifier_actual_vertex_input
end IV04.Paper.Computational
