module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Actual window scanning, copied frames and named recursive completion execution. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ScanDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorArithmetic.TTExecution

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

end
end Reference.LexTensorExecution
