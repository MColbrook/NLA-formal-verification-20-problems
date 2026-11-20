module

public import NLA.MD06.FiniteProbability.Definitions
public import Mathlib.Data.Nat.Log

@[expose] public section
set_option autoImplicit false
namespace Reference.RootMD06SpectralProbability
open Reference.MD06FiniteProbability
def TraceScale (k : ℕ) : ℕ := Nat.log 2 (Size k)
end Reference.RootMD06SpectralProbability
