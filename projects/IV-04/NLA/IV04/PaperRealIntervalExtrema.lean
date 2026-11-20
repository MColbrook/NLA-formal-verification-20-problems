module

public import NLA.IV04.PaperRealIntervalVertex
public import Mathlib.Data.Finset.Max

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section

theorem real_dense_interval_box_tridiagonal (n : ℕ) (pairs : List (ℚ × ℚ))
    (hsupport : rationalDenseEndpointAll n 0 0 pairs)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∀ (i j : Fin n), i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0 := by
  intro i j hoff
  have hl := rational_endpoint_vertex_tridiagonal n pairs (boxVertexCertificate n (fun _ => false)) hsupport i j hoff
  have hu := rational_endpoint_vertex_tridiagonal n pairs (boxVertexCertificate n (fun _ => true)) hsupport i j hoff
  rw [box_vertex_certificate_matrix] at hl hu
  change (pairs.getD (i.val*n+j.val) (0,0)).1=0 at hl
  change (pairs.getD (i.val*n+j.val) (0,0)).2=0 at hu
  have hb := hA i j
  change ((pairs.getD (i.val*n+j.val) (0,0)).1 : ℝ) ≤ A i j ∧
    A i j ≤ ((pairs.getD (i.val*n+j.val) (0,0)).2 : ℝ) at hb
  rw [hl,hu] at hb
  simpa only [Rat.cast_zero] using (le_antisymm hb.2 hb.1)

theorem actual_real_interval_determinant_maximum_vertex (n : ℕ) (pairs : List (ℚ × ℚ))
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    ∃ choices : List Bool, choices.length=n*n ∧
      IsGreatest (Matrix.det '' realDenseIntervalBox n pairs) ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  classical
  obtain ⟨choices,_,hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n × Fin n → Bool)) (fun choices => (rationalBoxVertex n pairs choices).det)
    Finset.univ_nonempty
  let cert := boxVertexCertificate n choices
  have hmat : rationalEndpointVertex n pairs cert=rationalBoxVertex n pairs choices := box_vertex_certificate_matrix n pairs choices
  refine ⟨cert,box_vertex_certificate_length n choices,⟨?_,?_⟩⟩
  · exact ⟨(rationalEndpointVertex n pairs cert).map (fun x => (x : ℝ)),
      actual_endpoint_vertex_in_real_box n pairs cert horder,(Rat.cast_det _).symm⟩
  · rintro value ⟨A,hA,rfl⟩
    obtain ⟨other,hother⟩ := real_box_endpoint_vertex_above n pairs A hA
    have hh := hmax other (Finset.mem_univ other)
    have hcast : ((rationalBoxVertex n pairs other).det : ℝ) ≤ ((rationalBoxVertex n pairs choices).det : ℝ) := by exact_mod_cast hh
    rw [hmat]
    exact hother.trans hcast

theorem actual_real_interval_determinant_minimum_vertex (n : ℕ) (pairs : List (ℚ × ℚ))
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    ∃ choices : List Bool, choices.length=n*n ∧
      IsLeast (Matrix.det '' realDenseIntervalBox n pairs) ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  classical
  obtain ⟨choices,_,hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset (Fin n × Fin n → Bool)) (fun choices => (rationalBoxVertex n pairs choices).det)
    Finset.univ_nonempty
  let cert := boxVertexCertificate n choices
  have hmat : rationalEndpointVertex n pairs cert=rationalBoxVertex n pairs choices := box_vertex_certificate_matrix n pairs choices
  refine ⟨cert,box_vertex_certificate_length n choices,⟨?_,?_⟩⟩
  · exact ⟨(rationalEndpointVertex n pairs cert).map (fun x => (x : ℝ)),
      actual_endpoint_vertex_in_real_box n pairs cert horder,(Rat.cast_det _).symm⟩
  · rintro value ⟨A,hA,rfl⟩
    obtain ⟨other,hother⟩ := real_box_endpoint_vertex_below n pairs A hA
    have hh := hmin other (Finset.mem_univ other)
    have hcast : ((rationalBoxVertex n pairs choices).det : ℝ) ≤ ((rationalBoxVertex n pairs other).det : ℝ) := by exact_mod_cast hh
    rw [hmat]
    exact hcast.trans hother

#print axioms actual_real_interval_determinant_maximum_vertex
#print axioms actual_real_interval_determinant_minimum_vertex
end
end IV04.Paper.Computational
