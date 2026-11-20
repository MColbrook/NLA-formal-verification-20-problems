module

public import NLA.MD06.CycleProfile.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open Set
def Root (R : ℕ) : ℝ := Classical.epsilon (fun t => t ∈ Icc 0 1 ∧ Balance R t = 2 * Real.pi)
end Reference.MD06CycleProfile
