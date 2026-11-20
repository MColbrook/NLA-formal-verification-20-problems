module

/- Actual charged candidate generation in the deficient first-cut rank branch. -/
public import NLA.TR04.OrderedTensorExecution.RuntimeBoundary
public import NLA.TR04.OrderedTensorSolver.SolverDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion

theorem actual_rank_le_candidate_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : (denseTensor A).rank≤r) :
    (candidateDataRun A (leftVectorMatrix (denseTensor A))
      (fun i : Fin m => singularValue (denseTensor A).transpose i.val) r rs).value=
      [Reference.OrderedTensorSolver.columnSpaceCompletion A rs] := by
  have hg : ¬r<(denseTensor A).rank := not_lt_of_ge hRank
  simp [candidateDataRun,actual_positive_scan_rank,hg,actual_prefix_completion_execution,
    Reference.OrderedTensorSolver.columnSpaceCompletion]

#print axioms actual_rank_le_candidate_execution
end
end Reference.OrderedTensorExecution
