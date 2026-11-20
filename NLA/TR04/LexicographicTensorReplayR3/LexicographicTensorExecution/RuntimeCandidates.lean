module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Charged candidate generation reproduces the verified ordered solver candidates. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.RuntimeRankCase
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.CandidateCorrectness
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.Strict
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

theorem actual_runtime_cyclic_completion {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (j : Fin (tensorBoundaryCount A r)) :
    (cyclicExecutionRun A (leftVectorMatrix (denseTensor A)) (sigmaOf (denseTensor A))
      (tensorBoundary A r) (tensorRetainedBoundary A r) j.val rs).value=cyclicCompletion A r rs j := by
  exact actual_cyclic_candidate_execution A (tensorBoundary A r) (tensorRetainedBoundary A r) j rs

theorem actual_candidate_generator_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hr : 0<r) :
    (candidatesExecutionRun A r rs).value=Reference.LexOrderedTensorSolver.candidates A r rs := by
  change (candidateDataRun A (leftVectorMatrix (denseTensor A)) (sigmaOf (denseTensor A)) r rs).value=_
  by_cases hRank : (denseTensor A).rank≤r
  · rw [actual_rank_le_candidate_execution A r rs hRank]
    simp [Reference.LexOrderedTensorSolver.candidates,hRank]
  · have hg : r<(denseTensor A).rank := lt_of_not_ge hRank
    have htau := actual_tensor_boundary_lookup A r hg
    have hp := actual_boundary_parameters (denseTensor A) r hr hg
    have ht : 0<tensorBoundaryCount A r := lt_of_lt_of_le hp.1 hp.2.1
    have hc0 := actual_runtime_cyclic_completion A r rs ⟨0,ht⟩
    have hz : hCount (denseTensor A) 0=(denseTensor A).rank := by
      rw [← actual_above_scan_length (denseTensor A) 0]
      exact actual_positive_scan_rank (denseTensor A)
    have htau' : (sigmaAtRun (sigmaOf (denseTensor A)) (r-1)).value=tensorBoundary A r := htau
    dsimp only [tensorBoundaryCount] at ht
    by_cases hf : tensorRetainedBoundary A r=tensorBoundaryCount A r
    · rw [hf] at hc0
      dsimp only [tensorBoundaryCount] at hc0
      dsimp only [tensorRetainedBoundary,tensorBoundaryCount] at hf
      simp [candidateDataRun,hz,hg,htau',actual_above_scan_length,actual_equal_scan_length,
        tensorRetainedBoundary,tensorBoundaryCount,hf,ht,hc0,
        Reference.LexOrderedTensorSolver.candidates,hRank]
    · dsimp only [tensorRetainedBoundary,tensorBoundaryCount] at hf
      simp only [candidateDataRun,value_bind,value_lessNat,value_branch,value_subNat,
        actual_above_scan_length,actual_equal_scan_length,hz,hg,decide_true,if_true,
        htau',value_equalNat,tensorRetainedBoundary,tensorBoundaryCount,
        hf,ht,decide_false,if_false,
        Reference.LexOrderedTensorSolver.candidates,hRank,dif_pos,List.ofFn_eq_map]
      simp only [Bool.false_eq_true,if_false,listMapRun_value]
      rw [actual_equal_scan_length (denseTensor A) (tensorBoundary A r)]
      apply congrArg (fun f => (List.finRange (tensorBoundaryCount A r)).map f)
      funext j
      exact actual_runtime_cyclic_completion A r rs j

#print axioms actual_candidate_generator_execution
end
end Reference.LexTensorExecution
