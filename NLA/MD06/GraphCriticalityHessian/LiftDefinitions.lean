module

public import NLA.MD06.GraphCriticalityHessian.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual

def PhaseLift {n : ℕ} (phi : Fin n → ℝ) : Phase n := fun i => (phi i : Real.Angle)
end Reference.MD06Actual
