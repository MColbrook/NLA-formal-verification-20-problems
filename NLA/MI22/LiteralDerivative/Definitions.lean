module

public import NLA.RA09.LiteralIntegral.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MI22.LiteralDerivative

/-- The positive scalar kernel in the printed root-Lipschitz proof. -/
def derivativeIntegrand (p m u : ℝ) : ℝ := u ^ p / (u+m)^2

end NLA.MI22.LiteralDerivative
