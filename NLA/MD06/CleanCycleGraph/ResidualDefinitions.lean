module

public import NLA.MD06.CleanCycleGraph.TopologyDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open Reference.MD06CycleProfile

def NodeResidual {ell R : ℕ} (x : TreeNodes ell R) : ℝ :=
  if x.1.val = R then -RootSign x.2.1 * Root R / (2 : ℝ)^(R-1) else 0
end Reference.MD06CleanCycle
