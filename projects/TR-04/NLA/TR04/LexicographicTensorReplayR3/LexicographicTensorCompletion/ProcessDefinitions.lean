module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Named actual recursive TT-SVD and prescribed-first-frame completion definitions.
Each primitive frame is prefix columns of the ACTUAL sorted Gram eigenbasis. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.Definitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.Layout
public import NLA.TR04.OptimalityEquality.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage

end
end Reference.LexTensorCompletion
