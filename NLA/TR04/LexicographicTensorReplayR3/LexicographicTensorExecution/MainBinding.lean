module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Literal concrete-layout arithmetic/SVD algorithm for the exact main.tex TR04 claims. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.GenuineProgramOptimal

@[expose] public section
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.LexTensorCompletion Reference.TensorOptimumAttainment

theorem modeCard_eq_prod (ns : List ℕ) : Reference.LexTensorArithmeticExecution.modeCard ns=ns.prod := by
  induction ns with
  | nil => exact Reference.LexTensorArithmeticExecution.modeCard_nil
  | cons n ns ih => rw [Reference.LexTensorArithmeticExecution.modeCard_cons,ih,List.prod_cons]

theorem actual_lexicographic_paper_algorithm {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a) :
    Reference.RecursiveTensorCompletion.feasible m (n::ns) (solverExecutionRun A r rs).value (r::rs) ∧
    0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length≤m ∧
    (0<optimalError A (r::rs) → Reference.RecursiveTensorCompletion.tensorFrobeniusSq
      (A-(solverExecutionRun A r rs).value)<((n::ns).length : ℝ)*optimalError A (r::rs)) ∧
    (optimalError A (r::rs)=0 → (solverExecutionRun A r rs).value=A) ∧
    charge (solverExecutionRun A r rs)≤1500*(m*(n::ns).prod)^5 := by
  have h:=actual_charged_solver_with_genuine_optimum A r rs hlen hr hns hm hmode
  refine ⟨(feasible_iff_original _ _).mp h.1,h.2.1,h.2.2.1,?_,h.2.2.2.2.1,?_⟩
  · simpa only [Reference.LexOrderedTensorSolver.error,tensorFrobeniusSq,
      Reference.RecursiveTensorCompletion.tensorFrobeniusSq,List.length_cons,Nat.cast_add,Nat.cast_one]
      using h.2.2.2.1
  · simpa only [Reference.LexTensorArithmeticExecution.denseSize,modeCard_eq_prod] using h.2.2.2.2.2

#print axioms actual_lexicographic_paper_algorithm
end
end Reference.LexTensorExecution
