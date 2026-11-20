module

public import NLA.TR04.CyclicBoundary.FullCompletion
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.CyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion
open scoped Matrix BigOperators

theorem verified_actual_boundary_candidate_count_le {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    eCount A tau ≤ m := by
  exact actual_boundary_candidate_count_le A tau

theorem verified_actual_cyclic_frame_dimension_and_optimality {m n : ℕ} (A : Rect m n)
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
  exact actual_cyclic_frame_dimension_and_optimality A r hr hrank j

theorem verified_actual_best_rank_cyclic_candidate_residual_bound {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hr : 0<r) (hrank : r<A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    ∃ j : Fin (eCount A (singularValue A (r-1))),
      frobeniusSq (candidateProjector A (singularValue A (r-1))
        (r-hCount A (singularValue A (r-1))) j*(A-B)) ≤
      ((r-hCount A (singularValue A (r-1)) : ℕ) : ℝ)/
        (eCount A (singularValue A (r-1)) : ℝ)*frobeniusSq (A-B) := by
  exact actual_best_rank_cyclic_candidate_residual_bound A B r hr hrank hB hbest

theorem verified_actual_full_tie_candidate_annihilates {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hr : 0<r) (hrank : r<A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hfull : r-hCount A (singularValue A (r-1))=eCount A (singularValue A (r-1)))
    (j : Fin (eCount A (singularValue A (r-1)))) :
    candidateProjector A (singularValue A (r-1)) (r-hCount A (singularValue A (r-1))) j*(A-B)=0 := by
  exact actual_full_tie_candidate_annihilates A B r hr hrank hB hbest hfull j

theorem verified_actual_tied_cyclic_completion_bound {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r) :
    ∃ j : Fin (tensorBoundaryCount A r),
      feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*(tensorRetainedBoundary A r : ℝ)/(tensorBoundaryCount A r : ℝ)*tensorFrobeniusSq (A-Y) := by
  exact actual_tied_cyclic_completion_bound A Y r rs hlen hr hrank hY hequal

theorem verified_actual_partial_tie_strict_completion {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r)
    (hpositive : 0<tensorFrobeniusSq (A-Y)) (hns : 0<ns.length)
    (hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r) :
    ∃ j : Fin (tensorBoundaryCount A r), feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j)<((ns.length : ℝ)+1)*tensorFrobeniusSq (A-Y) := by
  exact actual_partial_tie_strict_completion A Y r rs hlen hr hrank hY hequal hpositive hns hpartial

theorem verified_actual_full_tie_completion_bound {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r)
    (hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r) :
    ∃ j : Fin (tensorBoundaryCount A r),
      feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j) ≤ tensorFrobeniusSq (A-Y) := by
  exact actual_full_tie_completion_bound A Y r rs hlen hr hrank hY hequal hfull

#print axioms Reference.CyclicBoundary.verified_actual_boundary_candidate_count_le
#print axioms Reference.CyclicBoundary.verified_actual_cyclic_frame_dimension_and_optimality
#print axioms Reference.CyclicBoundary.verified_actual_best_rank_cyclic_candidate_residual_bound
#print axioms Reference.CyclicBoundary.verified_actual_full_tie_candidate_annihilates
#print axioms Reference.CyclicBoundary.verified_actual_tied_cyclic_completion_bound
#print axioms Reference.CyclicBoundary.verified_actual_partial_tie_strict_completion
#print axioms Reference.CyclicBoundary.verified_actual_full_tie_completion_bound
end
end Reference.CyclicBoundary
