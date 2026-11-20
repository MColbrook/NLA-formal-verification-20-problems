module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Exact first-minimum tie rule and full ordered solver execution semantics. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.RuntimeCandidates
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.RuntimeCounts
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.LexTensorCompletion

theorem actual_own_first_minimum_execution {m : ℕ} {ns : List ℕ}
    (A x : Tensor m ns) (xs : List (Tensor m ns)) :
    (liftRun (Reference.LexTensorArithmeticExecution.minimumRun A x xs)).value=
      Reference.LexOrderedTensorSolver.firstMinimum A x xs := by
  rw [value_lift,Reference.LexTensorArithmeticExecution.actual_first_minimum_execution]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : Reference.LexOrderedTensorSolver.error A y<Reference.LexOrderedTensorSolver.error A x
      · change tensorFrobeniusSq (A-y)<tensorFrobeniusSq (A-x) at h
        simp only [tensorFrobeniusSq,Matrix.sub_apply] at h
        simpa [Reference.TensorCandidateSelection.firstMinimum,Reference.LexOrderedTensorSolver.firstMinimum,
          Reference.TensorCandidateSelection.error,Reference.LexOrderedTensorSolver.error,
          tensorFrobeniusSq,Reference.RecursiveTensorCompletion.tensorFrobeniusSq,h] using ih y
      · change ¬tensorFrobeniusSq (A-y)<tensorFrobeniusSq (A-x) at h
        simp only [tensorFrobeniusSq,Matrix.sub_apply] at h
        simpa [Reference.TensorCandidateSelection.firstMinimum,Reference.LexOrderedTensorSolver.firstMinimum,
          Reference.TensorCandidateSelection.error,Reference.LexOrderedTensorSolver.error,
          tensorFrobeniusSq,Reference.RecursiveTensorCompletion.tensorFrobeniusSq,h] using ih x

theorem actual_full_solver_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hr : 0<r) (hm : 1≤m) :
    (solverExecutionRun A r rs).value=Reference.LexOrderedTensorSolver.solver A r rs := by
  have hcount := (actual_candidate_execution_count A r rs hm).1
  have hc := actual_candidate_generator_execution A r rs hr
  simp only [solverExecutionRun,value_bind]
  rw [hc]
  cases hs : Reference.LexOrderedTensorSolver.candidates A r rs with
  | nil => rw [hc,hs] at hcount; simp at hcount
  | cons x xs => simp only [Reference.LexOrderedTensorSolver.solver,hs,actual_own_first_minimum_execution]

#print axioms actual_full_solver_execution
end
end Reference.LexTensorExecution
