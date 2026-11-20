module

public import NLA.TR04.TensorCandidateSelection.Ordered
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorCandidateSelection
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.CyclicBoundary
open scoped Matrix BigOperators

theorem verified_solver_dominates {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    ∀ X ∈ candidates A r rs, error A (solver A r rs) ≤ error A X := by
  exact solver_dominates A r rs

theorem verified_actual_completion_count_le_first_mode {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 0<m) :
    (candidates A r rs).length ≤ m := by
  exact actual_completion_count_le_first_mode A r rs hm

theorem verified_columnSpaceCompletion_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hRank : (denseTensor A).rank ≤ r) :
    feasible m (n::ns) (columnSpaceCompletion A rs) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (columnSpaceCompletion A rs) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*error A Y := by
  exact columnSpaceCompletion_feasible_and_bound A r rs hlen hRank

theorem verified_solver_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (solver A r rs) ≤ singularTailSq (denseTensor A) r+(ns.length : ℝ)*error A Y := by
  exact solver_feasible_and_bound A r rs hlen hr

theorem verified_solver_strict_against_every_positive_feasible_comparator {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hY : feasible m (n::ns) Y (r::rs)) (hpositive : 0<error A Y) :
    error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y := by
  exact solver_strict_against_every_positive_feasible_comparator A Y r rs hlen hr hns hY hpositive

theorem verified_solver_recovers_any_zero_error_feasible_comparator {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hY : feasible m (n::ns) Y (r::rs)) (hzero : error A Y=0) : solver A r rs=A := by
  exact solver_recovers_any_zero_error_feasible_comparator A Y r rs hlen hr hY hzero

theorem verified_actual_solver_mathematical_guarantee {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length ≤ m ∧
      (∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) → 0<error A Y →
        error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y) ∧
      (∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) → error A Y=0 → solver A r rs=A) := by
  exact actual_solver_mathematical_guarantee A r rs hlen hr hns hm

theorem verified_firstMinimum_earliest_position {m : ℕ} {ns : List ℕ}
    (A acc x : Tensor m ns) (pre post : List (Tensor m ns))
    (hacc : error A x<error A acc) (hpre : ∀ y ∈ pre, error A x<error A y)
    (hpost : ∀ y ∈ post, error A x ≤ error A y) :
    firstMinimum A acc (pre++x::post)=x := by
  exact firstMinimum_earliest_position A acc x pre post hacc hpre hpost

theorem verified_rank_le_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : (denseTensor A).rank ≤ r) :
    candidates A r rs=[columnSpaceCompletion A rs] := by
  exact rank_le_candidate_list A r rs hRank

theorem verified_full_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r) :
    candidates A r rs=[cyclicCompletion A r rs ⟨0,ht⟩] := by
  exact full_tie_candidate_list A r rs hRank ht hfull

theorem verified_partial_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r) :
    candidates A r rs=List.ofFn (cyclicCompletion A r rs) := by
  exact partial_tie_candidate_list A r rs hRank ht hpartial

#print axioms Reference.TensorCandidateSelection.verified_solver_dominates
#print axioms Reference.TensorCandidateSelection.verified_actual_completion_count_le_first_mode
#print axioms Reference.TensorCandidateSelection.verified_columnSpaceCompletion_feasible_and_bound
#print axioms Reference.TensorCandidateSelection.verified_solver_feasible_and_bound
#print axioms Reference.TensorCandidateSelection.verified_solver_strict_against_every_positive_feasible_comparator
#print axioms Reference.TensorCandidateSelection.verified_solver_recovers_any_zero_error_feasible_comparator
#print axioms Reference.TensorCandidateSelection.verified_actual_solver_mathematical_guarantee
#print axioms Reference.TensorCandidateSelection.verified_firstMinimum_earliest_position
#print axioms Reference.TensorCandidateSelection.verified_rank_le_candidate_list
#print axioms Reference.TensorCandidateSelection.verified_full_tie_candidate_list
#print axioms Reference.TensorCandidateSelection.verified_partial_tie_candidate_list
end
end Reference.TensorCandidateSelection
