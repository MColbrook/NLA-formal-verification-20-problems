module

public import NLA.TR04.OrderedTensorSolver.GenuineOptimal
public import NLA.TR04.OrderedTensorSolver.IndexChecks
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion Reference.OrderedCyclicBoundary Reference.TensorOptimumAttainment
open scoped BigOperators Matrix

namespace Reference.OrderedIndex
theorem verified_indexList_ascending {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).SortedLT := by
  exact indexList_ascending p
end Reference.OrderedIndex

namespace Reference.OrderedTensorSolver
theorem verified_actual_completion_count_le_first_mode {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 0<m) :
    (candidates A r rs).length ≤ m := by
  exact actual_completion_count_le_first_mode A r rs hm
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_solver_mem {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    solver A r rs ∈ candidates A r rs := by
  exact solver_mem A r rs
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_firstMinimum_earliest_position {m : ℕ} {ns : List ℕ}
    (A acc x : Tensor m ns) (pre post : List (Tensor m ns))
    (hacc : error A x<error A acc) (hpre : ∀ y ∈ pre, error A x<error A y)
    (hpost : ∀ y ∈ post, error A x ≤ error A y) :
    firstMinimum A acc (pre++x::post)=x := by
  exact firstMinimum_earliest_position A acc x pre post hacc hpre hpost
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_rank_le_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : (denseTensor A).rank ≤ r) :
    candidates A r rs=[columnSpaceCompletion A rs] := by
  exact rank_le_candidate_list A r rs hRank
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_full_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r) :
    candidates A r rs=[cyclicCompletion A r rs ⟨0,ht⟩] := by
  exact full_tie_candidate_list A r rs hRank ht hfull
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_partial_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r) :
    candidates A r rs=List.ofFn (cyclicCompletion A r rs) := by
  exact partial_tie_candidate_list A r rs hRank ht hpartial
end Reference.OrderedTensorSolver

namespace Reference.OrderedTensorSolver
theorem verified_actual_ordered_solver_with_genuine_feasible_minimum {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length≤m ∧
      (0<optimalError A (r::rs) → error A (solver A r rs)<((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
      (optimalError A (r::rs)=0 → solver A r rs=A) := by
  exact actual_ordered_solver_with_genuine_feasible_minimum A r rs hlen hr hns hm
end Reference.OrderedTensorSolver

#print axioms Reference.OrderedIndex.verified_indexList_ascending
#print axioms Reference.OrderedTensorSolver.verified_actual_completion_count_le_first_mode
#print axioms Reference.OrderedTensorSolver.verified_solver_mem
#print axioms Reference.OrderedTensorSolver.verified_firstMinimum_earliest_position
#print axioms Reference.OrderedTensorSolver.verified_rank_le_candidate_list
#print axioms Reference.OrderedTensorSolver.verified_full_tie_candidate_list
#print axioms Reference.OrderedTensorSolver.verified_partial_tie_candidate_list
#print axioms Reference.OrderedTensorSolver.verified_actual_ordered_solver_with_genuine_feasible_minimum
end
