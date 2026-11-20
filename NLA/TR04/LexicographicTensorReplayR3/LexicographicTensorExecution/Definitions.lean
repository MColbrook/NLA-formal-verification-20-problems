module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Explicit exact arithmetic/SVD/equality and finite natural-index operations.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.SolverDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorArithmetic.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix

end
end Reference.LexTensorExecution
