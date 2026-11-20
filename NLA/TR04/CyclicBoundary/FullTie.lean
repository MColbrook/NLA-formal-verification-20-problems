module

/- Full-boundary specialization and actual candidate count for cyclic first-cut frames. -/
public import NLA.TR04.CyclicBoundary.Optimality

@[expose] public section

set_option autoImplicit false
namespace Reference.CyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix

theorem actual_boundary_candidate_count_le {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    eCount A tau ≤ m := by
  rw [eCount_eq_boundaryMultiplicity,← leftBoundaryProjector_rank_eq_multiplicity]
  exact Matrix.rank_le_height _

theorem actual_full_window_projector {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (j : Fin (eCount A tau)) : windowProjector A tau (eCount A tau) j=leftBoundaryProjector A tau := by
  have hmask : indicator (windowSelected A tau (eCount A tau) j)=
      (fun i : Fin m => if singularValue A.transpose i.val=tau then (1 : ℝ) else 0) := by
    funext i
    by_cases he : singularValue A.transpose i.val=tau
    · have hw : inWindow (eCount A tau) j (boundaryOrdinal A tau ⟨i,he⟩) := by
        let ii : Fin (eCount A tau) := boundaryOrdinal A tau ⟨i,he⟩
        exact (ii-j).isLt
      simp [indicator,windowSelected,he,hw]
    · simp [indicator,windowSelected,he]
  unfold windowProjector indicatorProjector leftBoundaryProjector
  rw [hmask]

theorem actual_full_tie_candidate_annihilates {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hr : 0<r) (hrank : r<A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hfull : r-hCount A (singularValue A (r-1))=eCount A (singularValue A (r-1)))
    (j : Fin (eCount A (singularValue A (r-1)))) :
    candidateProjector A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) j*(A-B)=0 := by
  have hcount : r-(leftAboveProjector A (singularValue A (r-1))).rank=
      (leftBoundaryProjector A (singularValue A (r-1))).rank := by
    rw [leftAboveProjector_rank_eq_multiplicity,leftBoundaryProjector_rank_eq_multiplicity]
    simpa only [hCount_eq_aboveMultiplicity,eCount_eq_boundaryMultiplicity] using hfull
  have h := (actual_best_rank_residual_above_and_full_boundary A B r hr hrank hB hbest).2 hcount
  rw [candidateProjector_split,hfull,actual_full_window_projector]
  exact h

#print axioms actual_boundary_candidate_count_le
#print axioms actual_full_window_projector
#print axioms actual_full_tie_candidate_annihilates
end
end Reference.CyclicBoundary