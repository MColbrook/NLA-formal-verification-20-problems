module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Exact first-cut optimality and residual bound for the actual cyclic candidate family. -/
public import NLA.TR04.LexicographicTensorSolver.CyclicEnergy

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix BigOperators

theorem actual_cyclic_frame_dimension_and_optimality {m n : ℕ} (A : Rect m n)
    (r : ℕ) (hr : 0<r) (hrank : r<A.rank)
    (j : Fin (eCount A (singularValue A (r-1)))) :
    Fintype.card {i : Fin m // selected A (singularValue A (r-1))
        (r-hCount A (singularValue A (r-1))) j i}=r ∧
    (candidateFrame A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) j).transpose*
        candidateFrame A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) j=1 ∧
    frobeniusSq (A-candidateProjector A (singularValue A (r-1))
        (r-hCount A (singularValue A (r-1))) j*A)=singularTailSq A r ∧
    ∀ B : Rect m n, B.rank ≤ r →
      frobeniusSq (A-candidateProjector A (singularValue A (r-1))
        (r-hCount A (singularValue A (r-1))) j*A) ≤ frobeniusSq (A-B) := by
  classical
  have hp := actual_boundary_parameters A r hr hrank
  have ht : 0<eCount A (singularValue A (r-1)) := lt_of_lt_of_le hp.1 hp.2.1
  let : NeZero (eCount A (singularValue A (r-1))) := ⟨ne_of_gt ht⟩
  have hc := selected_card A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) hp.2.1 j
  have he := actual_cyclic_projection_optimal_error A r hr hrank j
  refine ⟨hc.trans hp.2.2,(actual_candidate_frame A _ _ j).1,he,?_⟩
  intro B hB
  rw [he]
  exact singularTail_le_lowRankError A B r hB

theorem actual_best_rank_cyclic_candidate_residual_bound {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hr : 0<r) (hrank : r<A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    ∃ j : Fin (eCount A (singularValue A (r-1))),
      frobeniusSq (candidateProjector A (singularValue A (r-1))
        (r-hCount A (singularValue A (r-1))) j*(A-B)) ≤
      ((r-hCount A (singularValue A (r-1)) : ℕ) : ℝ)/
        (eCount A (singularValue A (r-1)) : ℝ)*frobeniusSq (A-B) := by
  have hp := actual_boundary_parameters A r hr hrank
  have ht : 0<eCount A (singularValue A (r-1)) := lt_of_lt_of_le hp.1 hp.2.1
  let : NeZero (eCount A (singularValue A (r-1))) := ⟨ne_of_gt ht⟩
  have hH := (actual_best_rank_residual_above_and_full_boundary A B r hr hrank hB hbest).1
  exact exists_actual_cyclic_candidate_small_residual A (A-B) (singularValue A (r-1))
    (r-hCount A (singularValue A (r-1))) hp.2.1 hH

#print axioms actual_cyclic_frame_dimension_and_optimality
#print axioms actual_best_rank_cyclic_candidate_residual_bound
end
end Reference.LexOrderedCyclicBoundary