module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine best-feasible tensor attainment for every finite actual unfolding rank tuple. -/
public import NLA.TR04.TensorOptimumAttainment.CompactSublevel

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection
open scoped Matrix.Norms.Elementwise

theorem actual_best_feasible_tensor_exists {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    ∃ B : Tensor m ns, feasible m ns B rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs → error A B≤error A Y := by
  let K : Set (Tensor m ns) := Metric.closedBall A (error A 0+1) ∩ feasibleSet m ns rs
  have hK : IsCompact K := (isCompact_closedBall A (error A 0+1)).inter_right
    (actual_tensor_feasible_isClosed m ns rs)
  have hz : (0 : Tensor m ns) ∈ K :=
    ⟨actual_error_sublevel_in_closedBall A 0 le_rfl,actual_zero_tensor_feasible m ns rs hlen⟩
  obtain ⟨B,hB,hmin⟩ := hK.exists_isMinOn ⟨0,hz⟩ (continuous_actual_error A).continuousOn
  refine ⟨B,hB.2,?_⟩
  intro Y hY
  by_cases h : error A Y≤error A 0
  · exact hmin ⟨actual_error_sublevel_in_closedBall A Y h,hY⟩
  · exact (hmin hz).trans (le_of_not_ge h)

#print axioms actual_best_feasible_tensor_exists
end
end Reference.TensorOptimumAttainment
