module

public import NLA.IV04.PaperRealIntervalVertexDefinitions
public import NLA.IV04.PaperCubeExtrema
public import NLA.IV04.PaperRationalEndpointVertex
public import NLA.IV04.PaperMatrixVertexDecision
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
noncomputable section
open scoped Matrix

theorem determinant_entry_affine_endpoints (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) (lower upper t : ℝ) :
    (Matrix.updateRow A i (Function.update (A i) j (((1-t)/2)*lower+((1+t)/2)*upper))).det=
      ((1-t)/2)*(Matrix.updateRow A i (Function.update (A i) j lower)).det+
        ((1+t)/2)*(Matrix.updateRow A i (Function.update (A i) j upper)).det := by
  have hr : Function.update (A i) j (((1-t)/2)*lower+((1+t)/2)*upper)=
      ((1-t)/2) • Function.update (A i) j lower+
        ((1+t)/2) • Function.update (A i) j upper := by
    ext k
    by_cases hk : k=j <;> simp [Function.update_apply,hk,Pi.smul_apply,smul_eq_mul] <;> ring
  rw [hr,Matrix.det_updateRow_add,Matrix.det_updateRow_smul,Matrix.det_updateRow_smul]

theorem normalized_box_update (n : ℕ) (pairs : List (ℚ × ℚ)) (q : Fin n × Fin n → ℝ)
    (c : Fin n × Fin n) (t : ℝ) :
    normalizedBoxMatrix n pairs (Function.update q c t)=
      Matrix.updateRow (normalizedBoxMatrix n pairs q) c.1
        (Function.update (normalizedBoxMatrix n pairs q c.1) c.2
          (((1-t)/2)*boxLowerReal n pairs c.1 c.2+((1+t)/2)*boxUpperReal n pairs c.1 c.2)) := by
  obtain ⟨i,j⟩ := c
  ext a b
  by_cases ha : a=i
  · subst a
    by_cases hb : b=j
    · subst b; simp [normalizedBoxMatrix]
    · simp [normalizedBoxMatrix,Function.update_apply,hb]
  · simp [normalizedBoxMatrix,Function.update_apply,ha]

theorem normalized_box_determinant_interpolation (n : ℕ) (pairs : List (ℚ × ℚ))
    (q : Fin n × Fin n → ℝ) (c : Fin n × Fin n) (t : ℝ) :
    (normalizedBoxMatrix n pairs (Function.update q c t)).det=
      ((1-t)/2)*(normalizedBoxMatrix n pairs (Function.update q c (-1))).det+
        ((1+t)/2)*(normalizedBoxMatrix n pairs (Function.update q c 1)).det := by
  rw [normalized_box_update,normalized_box_update,normalized_box_update]
  norm_num only [one_mul,zero_mul,zero_add,add_zero]
  exact determinant_entry_affine_endpoints n (normalizedBoxMatrix n pairs q) c.1 c.2
    (boxLowerReal n pairs c.1 c.2) (boxUpperReal n pairs c.1 c.2) t

theorem interval_scalar_parameter (lower upper a : ℝ) (hl : lower≤a) (hu : a≤upper) :
    ∃ t : ℝ, (-1≤t ∧ t≤1) ∧ ((1-t)/2)*lower+((1+t)/2)*upper=a := by
  by_cases he : lower=upper
  · refine ⟨0,by norm_num,?_⟩
    have ha : a=lower := by linarith
    rw [ha,← he]
    ring
  · have hp : 0<upper-lower := by
      by_contra h
      apply he
      apply le_antisymm (hl.trans hu)
      linarith
    refine ⟨(2*a-lower-upper)/(upper-lower),⟨?_,?_⟩,?_⟩
    · apply (le_div_iff₀ hp).mpr
      linarith
    · apply (div_le_iff₀ hp).mpr
      linarith
    · field_simp
      ring

theorem real_box_parameter_representation (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ q : Fin n × Fin n → ℝ, (∀ c, -1≤q c ∧ q c≤1) ∧ normalizedBoxMatrix n pairs q=A := by
  have hp : ∀ c : Fin n × Fin n, ∃ t : ℝ, (-1≤t ∧ t≤1) ∧
      ((1-t)/2)*boxLowerReal n pairs c.1 c.2+((1+t)/2)*boxUpperReal n pairs c.1 c.2=A c.1 c.2 :=
    fun c => interval_scalar_parameter _ _ _ (hA c.1 c.2).1 (hA c.1 c.2).2
  choose q hq using hp
  refine ⟨q,fun c => (hq c).1,?_⟩
  funext i j
  exact (hq (i,j)).2

theorem normalized_box_endpoint_matrix (n : ℕ) (pairs : List (ℚ × ℚ))
    (r : Fin n × Fin n → ℝ) (hr : ∀ c, r c=-1 ∨ r c=1) :
    normalizedBoxMatrix n pairs r=
      (rationalBoxVertex n pairs (fun c => decide (r c=1))).map (fun x => (x : ℝ)) := by
  ext i j
  rcases hr (i,j) with hm | hp
  · norm_num [normalizedBoxMatrix,rationalBoxVertex,boxLowerReal,boxUpperReal,hm,Matrix.map]
  · norm_num [normalizedBoxMatrix,rationalBoxVertex,boxLowerReal,boxUpperReal,hp,Matrix.map]

theorem real_box_endpoint_vertex_above (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : Fin n × Fin n → Bool, A.det ≤ ((rationalBoxVertex n pairs choices).det : ℝ) := by
  obtain ⟨q,hq,hrep⟩ := real_box_parameter_representation n pairs A hA
  obtain ⟨r,hr,_,hdet⟩ := IV04.Paper.affine_cube_vertex_above Finset.univ
    (fun q => (normalizedBoxMatrix n pairs q).det)
    (fun q c _ t => normalized_box_determinant_interpolation n pairs q c t) q (fun c _ => hq c)
  refine ⟨fun c => decide (r c=1),?_⟩
  rw [hrep,normalized_box_endpoint_matrix n pairs r (fun c => hr c (Finset.mem_univ c))] at hdet
  simpa only [← Rat.cast_det] using hdet

theorem real_box_endpoint_vertex_below (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : Fin n × Fin n → Bool, ((rationalBoxVertex n pairs choices).det : ℝ) ≤ A.det := by
  obtain ⟨q,hq,hrep⟩ := real_box_parameter_representation n pairs A hA
  obtain ⟨r,hr,_,hdet⟩ := IV04.Paper.affine_cube_vertex_below Finset.univ
    (fun q => (normalizedBoxMatrix n pairs q).det)
    (fun q c _ t => normalized_box_determinant_interpolation n pairs q c t) q (fun c _ => hq c)
  refine ⟨fun c => decide (r c=1),?_⟩
  rw [hrep,normalized_box_endpoint_matrix n pairs r (fun c => hr c (Finset.mem_univ c))] at hdet
  simpa only [← Rat.cast_det] using hdet

theorem row_major_coordinate_at (n : ℕ) (i j : Fin n)
    (hk : i.val*n+j.val<n*n) : rowMajorCoordinate n ⟨i.val*n+j.val,hk⟩=(i,j) := by
  have hp : 0<n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  apply Prod.ext <;> apply Fin.ext
  · change (i.val*n+j.val)/n=i.val
    rw [Nat.mul_comm i.val n,Nat.add_comm,Nat.add_mul_div_left _ _ hp,Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  · change (i.val*n+j.val)%n=j.val
    rw [Nat.mul_comm i.val n,Nat.add_comm,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt j.isLt]

theorem box_vertex_certificate_length (n : ℕ) (choices : Fin n × Fin n → Bool) :
    (boxVertexCertificate n choices).length=n*n := by simp [boxVertexCertificate]

theorem box_vertex_certificate_matrix (n : ℕ) (pairs : List (ℚ × ℚ))
    (choices : Fin n × Fin n → Bool) :
    rationalEndpointVertex n pairs (boxVertexCertificate n choices)=rationalBoxVertex n pairs choices := by
  ext i j
  have hk : i.val*n+j.val<n*n := by nlinarith [i.isLt,j.isLt]
  have hl : i.val*n+j.val<(boxVertexCertificate n choices).length := by rwa [box_vertex_certificate_length]
  have hc : (boxVertexCertificate n choices).getD (i.val*n+j.val) false=choices (i,j) := by
    rw [← List.getElem_eq_getD (l := boxVertexCertificate n choices) (h := hl) false]
    simp only [boxVertexCertificate,List.getElem_ofFn,row_major_coordinate_at n i j hk]
  rw [rationalEndpointVertex,selected_rational_endpoints_getD,hc]
  rfl

theorem real_box_actual_certificate_above (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : List Bool, choices.length=n*n ∧ A.det ≤ ((rationalEndpointVertex n pairs choices).det : ℝ) := by
  obtain ⟨choices,h⟩ := real_box_endpoint_vertex_above n pairs A hA
  exact ⟨boxVertexCertificate n choices,box_vertex_certificate_length n choices,by rwa [box_vertex_certificate_matrix]⟩

theorem real_box_actual_certificate_below (n : ℕ) (pairs : List (ℚ × ℚ))
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ realDenseIntervalBox n pairs) :
    ∃ choices : List Bool, choices.length=n*n ∧ ((rationalEndpointVertex n pairs choices).det : ℝ) ≤ A.det := by
  obtain ⟨choices,h⟩ := real_box_endpoint_vertex_below n pairs A hA
  exact ⟨boxVertexCertificate n choices,box_vertex_certificate_length n choices,by rwa [box_vertex_certificate_matrix]⟩

theorem actual_endpoint_vertex_in_real_box (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool)
    (horder : ∀ row ∈ pairs, row.1 ≤ row.2) :
    (rationalEndpointVertex n pairs choices).map (fun x => (x : ℝ)) ∈ realDenseIntervalBox n pairs := by
  intro i j
  have h := rational_endpoint_vertex_bounds n pairs choices horder i j
  constructor
  · change ((pairs.getD (i.val*n+j.val) (0,0)).1 : ℝ) ≤ (rationalEndpointVertex n pairs choices i j : ℝ)
    exact_mod_cast h.1
  · change (rationalEndpointVertex n pairs choices i j : ℝ) ≤ ((pairs.getD (i.val*n+j.val) (0,0)).2 : ℝ)
    exact_mod_cast h.2

theorem rational_vertex_language_exact_real_interval_language (matrix : List Bool) :
    matrix ∈ rationalMatrixVertexDecisionLanguage ↔ matrix ∈ rationalMatrixDeterminantDecisionLanguage := by
  constructor
  · rintro ⟨n,pairs,threshold,hr,hsize,ho,hs,choices,hlen,hdet⟩
    refine ⟨n,pairs,threshold,hr,hsize,ho,hs,
      (rationalEndpointVertex n pairs choices).map (fun x => (x : ℝ)),
      actual_endpoint_vertex_in_real_box n pairs choices ho,?_⟩
    rw [← Rat.cast_det]
    exact_mod_cast hdet
  · rintro ⟨n,pairs,threshold,hr,hsize,ho,hs,A,hA,hdet⟩
    obtain ⟨choices,hlen,hc⟩ := real_box_actual_certificate_above n pairs A hA
    refine ⟨n,pairs,threshold,hr,hsize,ho,hs,choices,hlen,?_⟩
    exact_mod_cast hdet.trans hc

theorem rational_matrix_determinant_decision_language_mem_np : rationalMatrixDeterminantDecisionLanguage ∈ Complexity.NP := by
  have he : rationalMatrixDeterminantDecisionLanguage=rationalMatrixVertexDecisionLanguage :=
    Set.ext (fun matrix => (rational_vertex_language_exact_real_interval_language matrix).symm)
  rw [he]
  exact rational_matrix_vertex_decision_language_mem_np

#print axioms rational_matrix_determinant_decision_language_mem_np
end
end IV04.Paper.Computational
