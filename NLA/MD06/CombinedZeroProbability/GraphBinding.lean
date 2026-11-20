module

public import NLA.MD06.CombinedZeroProbability.Conditioning
public import NLA.MD06.GraphCycleEvent.Proofs

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Reference.MD06FiniteProbability Reference.MD06GraphCycleEvent
open Filter Topology

theorem actual_uniform_simple_cubic_no_cycle_limit (ell : ℕ) (hell : 3≤ell) :
    Tendsto (fun k => GraphProbability k (fun G => ¬GraphCycleExists G ell)) atTop
      (𝓝 (Real.exp (-((2 : ℝ)^ell/(2*(ell : ℝ)))))) := by
  have h := actual_simple_conditioned_no_cycle_limit ell hell
  simpa only [SimpleNoCycleProbability,←actual_uniform_graph_no_cycle_probability hell] using h

#print axioms actual_uniform_simple_cubic_no_cycle_limit
end Reference.MD06CombinedZero
