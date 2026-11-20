module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual literal projected-residual averaging for the concrete tied cyclic family. -/
public import NLA.TR04.LexicographicTensorSolver.CyclicFrames

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RealColumnCompression
open scoped Matrix BigOperators

theorem indicatorProjector_frobenius_le {m n : ℕ} (V : Square m) (hV : IsOrthogonal V)
    (p : Fin m → Prop) (R : Rect m n) :
    frobeniusSq (indicatorProjector V p*R) ≤ frobeniusSq R := by
  classical
  rw [indicatorProjector_frobenius V hV]
  calc
    _ ≤ ∑ i : Fin m, ∑ b : Fin n, (V.transpose*R) i b^2 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : p i
      · simp [indicator,hp]
      · simp only [indicator,if_neg hp,zero_mul]
        exact Finset.sum_nonneg (fun b hb => sq_nonneg _)
    _ = frobeniusSq (V.transpose*R) := rfl
    _ = _ := frobeniusSq_frame_mul V.transpose (by simpa using hV.2) R

theorem actual_candidate_residual_sum {m n : ℕ} (A R : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau)
    (hH : leftAboveProjector A tau*R=0) :
    (∑ j : Fin (eCount A tau), frobeniusSq (candidateProjector A tau s j*R))=
      (s : ℝ)*frobeniusSq (leftBoundaryProjector A tau*R) := by
  have he : ∀ j : Fin (eCount A tau), candidateProjector A tau s j*R=windowProjector A tau s j*R := by
    intro j
    rw [candidateProjector_split,Matrix.add_mul,hH,zero_add]
  simp_rw [he]
  exact actual_cyclic_projected_error_sum A R tau s hs

theorem actual_candidate_residual_average_le {m n : ℕ} (A R : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau)
    (hH : leftAboveProjector A tau*R=0) :
    (∑ j : Fin (eCount A tau), frobeniusSq (candidateProjector A tau s j*R)) ≤
      (s : ℝ)*frobeniusSq R := by
  rw [actual_candidate_residual_sum A R tau s hs hH]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact indicatorProjector_frobenius_le (leftVectorMatrix A) (leftVectorMatrix_orthogonal A)
    (fun i => singularValue A.transpose i.val=tau) R

theorem exists_actual_cyclic_candidate_small_residual {m n : ℕ} (A R : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau)
    (hH : leftAboveProjector A tau*R=0) :
    ∃ j : Fin (eCount A tau), frobeniusSq (candidateProjector A tau s j*R) ≤
      (s : ℝ)/(eCount A tau : ℝ)*frobeniusSq R := by
  classical
  have ht : (0 : ℝ)<(eCount A tau : ℝ) := by exact_mod_cast NeZero.pos (eCount A tau)
  have ha := actual_candidate_residual_average_le A R tau s hs hH
  have hb : (∑ j : Fin (eCount A tau), (s : ℝ)/(eCount A tau : ℝ)*frobeniusSq R)=
      (s : ℝ)*frobeniusSq R := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hc : (∑ j : Fin (eCount A tau), frobeniusSq (candidateProjector A tau s j*R)) ≤
      ∑ j : Fin (eCount A tau), (s : ℝ)/(eCount A tau : ℝ)*frobeniusSq R := by rw [hb];exact ha
  obtain ⟨j,hj,h⟩ := Finset.exists_le_of_sum_le (Finset.univ_nonempty : (Finset.univ : Finset (Fin (eCount A tau))).Nonempty) hc
  exact ⟨j,h⟩

#print axioms actual_candidate_residual_sum
#print axioms actual_candidate_residual_average_le
#print axioms exists_actual_cyclic_candidate_small_residual
end
end Reference.LexOrderedCyclicBoundary