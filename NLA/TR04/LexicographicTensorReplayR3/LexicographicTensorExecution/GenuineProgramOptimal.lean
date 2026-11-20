module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Actual charged indexed-array program: all ranks, true optimum and exact recovery. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.RuntimeSolver
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.WholeCharge
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.GenuineOptimal
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.LexTensorCompletion Reference.TensorOptimumAttainment

theorem actual_charged_solver_with_genuine_optimum {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    feasible m (n::ns) (solverExecutionRun A r rs).value (r::rs) ∧
    0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length≤m ∧
    (0<optimalError A (r::rs) → Reference.LexOrderedTensorSolver.error A (solverExecutionRun A r rs).value<
      ((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
    (optimalError A (r::rs)=0 → (solverExecutionRun A r rs).value=A) ∧
    charge (solverExecutionRun A r rs)≤1500*(Reference.LexTensorArithmeticExecution.denseSize m (n::ns))^5 := by
  have hs := actual_full_solver_execution A r rs hr hm
  have hc := actual_candidate_execution_count A r rs hm
  have ho := Reference.LexOrderedTensorSolver.actual_ordered_solver_with_genuine_feasible_minimum
    A r rs hlen hr hns (by omega)
  have ht := actual_full_solver_dense_polynomial_charge A r rs hm hmode
  exact ⟨by simpa only [hs] using ho.1,hc.1,hc.2,
    by simpa only [hs] using ho.2.2.1,by simpa only [hs] using ho.2.2.2,ht⟩

#print axioms actual_charged_solver_with_genuine_optimum
end
end Reference.LexTensorExecution
