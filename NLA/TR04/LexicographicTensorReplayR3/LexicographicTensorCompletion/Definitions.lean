module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Concrete lexicographic recursion on literal finite tensor indices. -/
public import NLA.TR04.RecursiveTensorCompletion.Definitions
public import NLA.TR04.LexicographicFeasibilityBridge.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker
end
end Reference.LexTensorCompletion
