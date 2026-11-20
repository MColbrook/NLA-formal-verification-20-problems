module

public import NLA.IV04.PaperRealIntervalExtrema
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section

theorem verified_normalized_box_determinant_interpolation (n : ℕ) (pairs : List (ℚ × ℚ))
    (q : Fin n × Fin n → ℝ) (c : Fin n × Fin n) (t : ℝ) :
    (normalizedBoxMatrix n pairs (Function.update q c t)).det=
      ((1-t)/2)*(normalizedBoxMatrix n pairs (Function.update q c (-1))).det+
        ((1+t)/2)*(normalizedBoxMatrix n pairs (Function.update q c 1)).det := by
  exact normalized_box_determinant_interpolation n pairs q c t

theorem verified_real_box_actual_certificate_above (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : List Bool, choices.length=n*n ∧ A.det ≤ ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  exact real_box_actual_certificate_above n pairs A hA

theorem verified_real_box_actual_certificate_below (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : List Bool, choices.length=n*n ∧ ((rationalEndpointVertex n pairs choices).det : ℝ) ≤ A.det := by
  exact real_box_actual_certificate_below n pairs A hA

theorem verified_box_vertex_certificate_length (n : ℕ) (choices : Fin n × Fin n → Bool) :
    (boxVertexCertificate n choices).length=n*n := by
  exact box_vertex_certificate_length n choices

theorem verified_box_vertex_certificate_matrix (n : ℕ) (pairs : List (ℚ × ℚ))
    (choices : Fin n × Fin n → Bool) :
    rationalEndpointVertex n pairs (boxVertexCertificate n choices)=rationalBoxVertex n pairs choices := by
  exact box_vertex_certificate_matrix n pairs choices

theorem verified_actual_endpoint_vertex_in_real_box (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    (rationalEndpointVertex n pairs choices).map (fun x => (x : ℝ)) ∈ realDenseIntervalBox n pairs := by
  exact actual_endpoint_vertex_in_real_box n pairs choices horder

theorem verified_real_dense_interval_box_tridiagonal (n : ℕ) (pairs : List (ℚ × ℚ))
    (hsupport : rationalDenseEndpointAll n 0 0 pairs)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∀ (i j : Fin n), i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0 := by
  exact real_dense_interval_box_tridiagonal n pairs hsupport A hA

theorem verified_actual_real_interval_determinant_maximum_vertex (n : ℕ) (pairs : List (ℚ × ℚ))
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    ∃ choices : List Bool, choices.length=n*n ∧
      IsGreatest (Matrix.det '' realDenseIntervalBox n pairs) ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  exact actual_real_interval_determinant_maximum_vertex n pairs horder

theorem verified_actual_real_interval_determinant_minimum_vertex (n : ℕ) (pairs : List (ℚ × ℚ))
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    ∃ choices : List Bool, choices.length=n*n ∧
      IsLeast (Matrix.det '' realDenseIntervalBox n pairs) ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  exact actual_real_interval_determinant_minimum_vertex n pairs horder

theorem verified_rational_vertex_language_exact_real_interval_language (matrix : List Bool) :
    matrix ∈ rationalMatrixVertexDecisionLanguage ↔ matrix ∈ rationalMatrixDeterminantDecisionLanguage := by
  exact rational_vertex_language_exact_real_interval_language matrix

theorem verified_rational_matrix_determinant_decision_language_mem_np : rationalMatrixDeterminantDecisionLanguage ∈ Complexity.NP := by
  exact rational_matrix_determinant_decision_language_mem_np

#print axioms IV04.Paper.Computational.verified_normalized_box_determinant_interpolation
#print axioms IV04.Paper.Computational.verified_real_box_actual_certificate_above
#print axioms IV04.Paper.Computational.verified_real_box_actual_certificate_below
#print axioms IV04.Paper.Computational.verified_box_vertex_certificate_length
#print axioms IV04.Paper.Computational.verified_box_vertex_certificate_matrix
#print axioms IV04.Paper.Computational.verified_actual_endpoint_vertex_in_real_box
#print axioms IV04.Paper.Computational.verified_real_dense_interval_box_tridiagonal
#print axioms IV04.Paper.Computational.verified_actual_real_interval_determinant_maximum_vertex
#print axioms IV04.Paper.Computational.verified_actual_real_interval_determinant_minimum_vertex
#print axioms IV04.Paper.Computational.verified_rational_vertex_language_exact_real_interval_language
#print axioms IV04.Paper.Computational.verified_rational_matrix_determinant_decision_language_mem_np
end
end IV04.Paper.Computational
