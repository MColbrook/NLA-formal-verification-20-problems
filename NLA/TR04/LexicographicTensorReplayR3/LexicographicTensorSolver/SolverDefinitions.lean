module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Literal ordered candidates and first-minimum selection. Pure definitions.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.CompletionDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedTensorSolver
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

end
end Reference.LexOrderedTensorSolver