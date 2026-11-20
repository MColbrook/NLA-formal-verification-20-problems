module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine closed actual unfolding-rank constraints and literal feasible optimum definitions. -/
public import NLA.TR04.TensorCandidateSelection.Definitions
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection

def feasibleSet (m : ℕ) (ns : List ℕ) (rs : List ℕ) : Set (Tensor m ns) :=
  {Y | feasible m ns Y rs}

def optimalError {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (rs : List ℕ) : ℝ :=
  sInf (error A '' feasibleSet m ns rs)

end
end Reference.TensorOptimumAttainment
