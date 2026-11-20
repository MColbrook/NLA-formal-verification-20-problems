module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- The new ascending-index algorithm has its own actual attained-minimum guarantee. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.Ordered
public import NLA.TR04.TensorOptimumAttainment.OptimalBound
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.FeasibleBridge

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexOrderedTensorSolver
noncomputable section
open Reference.LexTensorCompletion Reference.TensorOptimumAttainment

theorem actual_ordered_solver_with_genuine_feasible_minimum {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length≤m ∧
      (0<optimalError A (r::rs) → error A (solver A r rs)<((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
      (optimalError A (r::rs)=0 → solver A r rs=A) := by
  obtain ⟨B,hB,hE,_⟩ := actual_optimal_error_attained A (r::rs) (by simpa using hlen)
  have hBlex := (feasible_iff_original B (r::rs)).mpr hB
  change error A B=optimalError A (r::rs) at hE
  have h := actual_solver_mathematical_guarantee A r rs hlen hr hns hm
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro hp
    have hpB : 0<error A B := by rw [hE];exact hp
    simpa only [hE] using h.2.2.1 B hBlex hpB
  · intro hz
    exact h.2.2.2 B hBlex (hE.trans hz)

#print axioms actual_ordered_solver_with_genuine_feasible_minimum
end
end Reference.LexOrderedTensorSolver
