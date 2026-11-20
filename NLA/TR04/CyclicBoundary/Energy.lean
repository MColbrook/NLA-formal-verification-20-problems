module

/- Genuine actual sorted-Gram cyclic selection energy and first-cut optimality. -/
public import NLA.TR04.CyclicBoundary.Averaging

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.CyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RealColumnCompression
open scoped Matrix BigOperators

theorem actual_gram_row_energy {m n : ℕ} (A : Rect m n) (i : Fin m) :
    (∑ b : Fin n, ((leftVectorMatrix A).transpose*A) i b^2)=singularValue A.transpose i.val^2 := by
  let V := leftVectorMatrix A
  let C := V.transpose*A
  have hg := congrFun (congrFun (leftVectorMatrix_gram_diagonal A) i) i
  have hm : C*C.transpose=V.transpose*(A*A.transpose)*V := by
    simp only [C,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
  have hr : (C*C.transpose) i i=∑ b : Fin n, C i b^2 := by
    simp only [Matrix.mul_apply,Matrix.transpose_apply,pow_two]
  rw [← hm,hr,Matrix.diagonal_apply_eq] at hg
  exact hg

theorem actual_mask_captured_energy {m n : ℕ} (A : Rect m n) (p : Fin m → Prop) :
    frobeniusSq (indicatorProjector (leftVectorMatrix A) p*A)=
      ∑ i : Fin m, indicator p i*singularValue A.transpose i.val^2 := by
  rw [indicatorProjector_frobenius _ (leftVectorMatrix_orthogonal A)]
  simp_rw [actual_gram_row_energy]

theorem boundary_mask_energy {m n : ℕ} (A : Rect m n) (tau : ℝ) (p : Fin m → Prop)
    (hp : ∀ i : Fin m, p i → singularValue A.transpose i.val=tau) :
    (∑ i : Fin m, indicator p i*singularValue A.transpose i.val^2)=
      (Fintype.card {i : Fin m // p i} : ℝ)*tau^2 := by
  calc
    _ = ∑ i : Fin m, indicator p i*tau^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : p i
      · rw [hp i h]
      · simp [indicator,h]
    _ = _ := by rw [← Finset.sum_mul,indicator_sum_eq_card]

theorem actual_window_captured_energy {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (j : Fin (eCount A tau)) :
    frobeniusSq (windowProjector A tau s j*A)=(s : ℝ)*tau^2 := by
  rw [windowProjector,actual_mask_captured_energy,boundary_mask_energy]
  · rw [window_card A tau s hs j]
  · intro i hi
    by_contra he
    simp [windowSelected,he] at hi

theorem actual_candidate_captured_energy {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (j : Fin (eCount A tau)) :
    frobeniusSq (candidateProjector A tau s j*A)=
      frobeniusSq (leftAboveProjector A tau*A)+(s : ℝ)*tau^2 := by
  classical
  have hmask : ∀ i : Fin m, indicator (selected A tau s j) i=
      indicator (fun i => tau<singularValue A.transpose i.val) i+indicator (windowSelected A tau s j) i := by
    intro i
    by_cases ha : tau<singularValue A.transpose i.val
    · have he : singularValue A.transpose i.val≠tau := ne_of_gt ha
      simp [indicator,selected,windowSelected,ha,he]
    · simp [indicator,selected,ha]
  have hH : leftAboveProjector A tau=indicatorProjector (leftVectorMatrix A)
      (fun i => tau<singularValue A.transpose i.val) := rfl
  rw [candidateProjector,actual_mask_captured_energy,hH,actual_mask_captured_energy]
  calc
    _ = (∑ i : Fin m, indicator (fun i => tau<singularValue A.transpose i.val) i*singularValue A.transpose i.val^2)+
        ∑ i : Fin m, indicator (windowSelected A tau s j) i*singularValue A.transpose i.val^2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmask i,add_mul]
    _ = _ := by
      have hw := actual_window_captured_energy A tau s hs j
      change frobeniusSq (indicatorProjector (leftVectorMatrix A) (windowSelected A tau s j)*A)=_ at hw
      rw [actual_mask_captured_energy] at hw
      rw [hw]

theorem actual_leading_captured_energy {m n : ℕ} (A : Rect m n) (r : ℕ)
    (hr : 0<r) (hrank : r<A.rank) :
    frobeniusSq (leftLeadingProjector A r*A)=
      frobeniusSq (leftAboveProjector A (singularValue A (r-1))*A)+
        ((r-hCount A (singularValue A (r-1)) : ℕ) : ℝ)*singularValue A (r-1)^2 := by
  classical
  let tau := singularValue A (r-1)
  let pS := fun i : Fin m => singularValue A.transpose i.val=tau ∧ i.val<r
  have hmask : ∀ i : Fin m, indicator (fun i => i.val<r) i=
      indicator (fun i => tau<singularValue A.transpose i.val) i+indicator pS i := by
    intro i
    by_cases hh : i.val<r
    · have hle : tau ≤ singularValue A.transpose i.val := by
        simpa only [tau,singularValue_transpose] using (singular_values_semantics A).2.1 (show i.val ≤ r-1 by omega)
      by_cases he : singularValue A.transpose i.val=tau
      · simp [indicator,pS,he,hh]
      · have ha : tau<singularValue A.transpose i.val := lt_of_le_of_ne hle (Ne.symm he)
        simp [indicator,pS,he,hh,ha]
    · have ha : ¬ tau<singularValue A.transpose i.val := by
        intro hi
        exact hh (above_boundary_index_lt_rank_parameter A r i hi)
      simp [indicator,pS,hh,ha]
  let oldF : Fintype {i : Fin m // pS i} := inferInstance
  have hs : @Fintype.card {i : Fin m // pS i} oldF=r-hCount A tau := by
    rw [Fintype.card_subtype,hCount_eq_aboveMultiplicity]
    simpa only [pS,retainedBoundaryMultiplicity,Finset.filter_filter] using
      retained_boundary_multiplicity_eq_rank_sub_above A r hr hrank
  let newF : Fintype {i : Fin m // pS i} := @Subtype.fintype (Fin m) pS
    (fun i => Classical.propDecidable (pS i)) (Fin.fintype m)
  have hsClassical : @Fintype.card {i : Fin m // pS i} newF=r-hCount A tau :=
    (@Fintype.card_congr {i : Fin m // pS i} {i : Fin m // pS i} newF oldF (Equiv.refl _)).trans hs
  have hL : leftLeadingProjector A r=indicatorProjector (leftVectorMatrix A) (fun i => i.val<r) := by
    have hm : headMask m r=indicator (fun i : Fin m => i.val<r) := by
      funext i
      by_cases h : i.val<r <;> simp [headMask,indicator,h]
    unfold leftLeadingProjector indicatorProjector
    rw [hm]
  have hH : leftAboveProjector A tau=indicatorProjector (leftVectorMatrix A) (fun i => tau<singularValue A.transpose i.val) := rfl
  rw [hL,actual_mask_captured_energy]
  change _ = frobeniusSq (leftAboveProjector A tau*A)+((r-hCount A tau : ℕ) : ℝ)*tau^2
  rw [hH,actual_mask_captured_energy]
  calc
    _ = (∑ i : Fin m, indicator (fun i => tau<singularValue A.transpose i.val) i*singularValue A.transpose i.val^2)+
        ∑ i : Fin m, indicator pS i*singularValue A.transpose i.val^2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hmask i,add_mul]
    _ = _ := by
      rw [boundary_mask_energy A tau pS (fun i hi => hi.1)]
      congr 1
      exact congrArg (fun z : ℕ => (z : ℝ)*tau^2) hsClassical

theorem indicator_projection_error_energy {m n : ℕ} (A : Rect m n) (V : Square m)
    (hV : IsOrthogonal V) (p : Fin m → Prop) :
    frobeniusSq A=frobeniusSq (A-indicatorProjector V p*A)+frobeniusSq (indicatorProjector V p*A) := by
  let U := indicatorFrame V p
  have hU := indicatorFrame_orthonormal V hV p
  have hP := indicatorFrame_projector V p
  have he := orthonormal_column_error_decomposition U hU A (0 : Rect (Fintype.card {i : Fin m // p i}) n)
  simp only [Matrix.mul_zero,sub_zero] at he
  have hn := frobeniusSq_frame_mul U hU (U.transpose*A)
  rw [← hn,← Matrix.mul_assoc,hP] at he
  exact he

theorem actual_leading_projection_error {m n : ℕ} (A : Rect m n) (r : ℕ) :
    frobeniusSq (A-leftLeadingProjector A r*A)=singularTailSq A r := by
  let V := leftVectorMatrix A
  have hV := leftVectorMatrix_orthogonal A
  have hd := leftVectorMatrix_gram_diagonal A
  have hp : leftLeadingProjector A r*A=(realTruncation A.transpose r V).transpose := by
    simp only [leftLeadingProjector,realTruncation,Matrix.transpose_mul,
      Matrix.diagonal_transpose,Matrix.transpose_transpose,Matrix.mul_assoc,V]
  rw [hp]
  calc
    _ = frobeniusSq (A.transpose-realTruncation A.transpose r V) := by
      simpa only [Matrix.transpose_sub,Matrix.transpose_transpose] using
        frobeniusSq_transpose (A.transpose-realTruncation A.transpose r V)
    _ = singularTailSq A.transpose r := realTruncation_error A.transpose r V hV
      (by simpa only [Matrix.transpose_transpose] using hd)
    _ = _ := singularTailSq_transpose A r

theorem actual_cyclic_projection_optimal_error {m n : ℕ} (A : Rect m n) (r : ℕ)
    (hr : 0<r) (hrank : r<A.rank) [NeZero (eCount A (singularValue A (r-1)))]
    (j : Fin (eCount A (singularValue A (r-1)))) :
    frobeniusSq (A-candidateProjector A (singularValue A (r-1))
      (r-hCount A (singularValue A (r-1))) j*A)=singularTailSq A r := by
  have hs := (actual_boundary_parameters A r hr hrank).2.1
  have he := actual_candidate_captured_energy A (singularValue A (r-1))
    (r-hCount A (singularValue A (r-1))) hs j
  have hl := actual_leading_captured_energy A r hr hrank
  have hV := leftVectorMatrix_orthogonal A
  have hc := indicator_projection_error_energy A (leftVectorMatrix A) hV
    (selected A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) j)
  have hlead := indicator_projection_error_energy A (leftVectorMatrix A) hV (fun i => i.val<r)
  have hlo := actual_leading_projection_error A r
  have hL : leftLeadingProjector A r=indicatorProjector (leftVectorMatrix A) (fun i => i.val<r) := by
    have hm : headMask m r=indicator (fun i : Fin m => i.val<r) := by
      funext i
      by_cases h : i.val<r <;> simp [headMask,indicator,h]
    unfold leftLeadingProjector indicatorProjector
    rw [hm]
  rw [← hL] at hlead
  change frobeniusSq A=frobeniusSq (A-candidateProjector A (singularValue A (r-1))
    (r-hCount A (singularValue A (r-1))) j*A)+frobeniusSq (candidateProjector A (singularValue A (r-1))
    (r-hCount A (singularValue A (r-1))) j*A) at hc
  linarith

#print axioms actual_gram_row_energy
#print axioms actual_candidate_captured_energy
#print axioms actual_cyclic_projection_optimal_error
end
end Reference.CyclicBoundary