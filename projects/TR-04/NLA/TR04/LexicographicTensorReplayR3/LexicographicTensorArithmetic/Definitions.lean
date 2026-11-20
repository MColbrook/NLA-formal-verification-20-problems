module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Exact structured arithmetic and singular-subspace interpreter.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex.
A trace records actual scalar operands; each interpreter call produces its result.
No supplied runtime, solver instruction, or correctness contract is present. -/
public import NLA.TR04.TensorCandidateSelection.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix

end
end Reference.LexTensorArithmeticExecution
