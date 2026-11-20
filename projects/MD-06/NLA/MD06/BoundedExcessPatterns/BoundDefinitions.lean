module

public import NLA.MD06.BoundedExcessPatterns.EventDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open scoped BigOperators
def BoundConstant (K : ℕ) : ℝ :=
  ∑s : ExcessShape K,((2^(9*s.val.1.val^2) : ℕ) : ℝ)*(2/(3 : ℝ)^s.val.2.val)
end Reference.MD06BoundedExcess
