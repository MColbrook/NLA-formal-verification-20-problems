module

/- Exact first-minimum tie rule and full ordered solver execution semantics. -/
public import NLA.TR04.OrderedTensorExecution.RuntimeCandidates
public import NLA.TR04.OrderedTensorExecution.RuntimeCounts
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RecursiveTensorCompletion

theorem actual_own_first_minimum_execution {m : ℕ} {ns : List ℕ}
    (A x : Tensor m ns) (xs : List (Tensor m ns)) :
    (liftRun (Reference.TensorArithmeticExecution.minimumRun A x xs)).value=
      Reference.OrderedTensorSolver.firstMinimum A x xs := by
  rw [value_lift,Reference.TensorArithmeticExecution.actual_first_minimum_execution]
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : Reference.OrderedTensorSolver.error A y<Reference.OrderedTensorSolver.error A x
      · change tensorFrobeniusSq (A-y)<tensorFrobeniusSq (A-x) at h
        simpa [Reference.TensorCandidateSelection.firstMinimum,Reference.OrderedTensorSolver.firstMinimum,
          Reference.TensorCandidateSelection.error,Reference.OrderedTensorSolver.error,h] using ih y
      · change ¬tensorFrobeniusSq (A-y)<tensorFrobeniusSq (A-x) at h
        simpa [Reference.TensorCandidateSelection.firstMinimum,Reference.OrderedTensorSolver.firstMinimum,
          Reference.TensorCandidateSelection.error,Reference.OrderedTensorSolver.error,h] using ih x

theorem actual_full_solver_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hr : 0<r) (hm : 1≤m) :
    (solverExecutionRun A r rs).value=Reference.OrderedTensorSolver.solver A r rs := by
  have hcount := (actual_candidate_execution_count A r rs hm).1
  have hc := actual_candidate_generator_execution A r rs hr
  simp only [solverExecutionRun,value_bind]
  rw [hc]
  cases hs : Reference.OrderedTensorSolver.candidates A r rs with
  | nil => rw [hc,hs] at hcount; simp at hcount
  | cons x xs => simp only [Reference.OrderedTensorSolver.solver,hs,actual_own_first_minimum_execution]

#print axioms actual_full_solver_execution
end
end Reference.OrderedTensorExecution
