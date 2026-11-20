module

public import NLA.MD06.NonbacktrackingFoundation.Definitions
public import NLA.MD06.CubicConfiguration.UniformDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06Nonbacktracking
open scoped BigOperators

def PairingMean (n : ℕ) (f : Pairing n → ℝ) : ℝ :=
  (∑ p : Pairing n,f p)/(Fintype.card (Pairing n) : ℝ)

def MeanNonbacktrackingTrace (n t : ℕ) : ℝ :=
  PairingMean n (fun p=>Matrix.trace (NonbacktrackingMatrix p ^ t))

end Reference.MD06WalkExposure
