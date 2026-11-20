module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Pure concrete cyclic candidate completions, each using named actual recursive TT-SVD. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.CyclicDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.ProcessDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

end
end Reference.LexOrderedCyclicBoundary