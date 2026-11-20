module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual cyclic windows of the tied sorted Gram eigenspace. Pure definitions.
Reference extension of OpenProblemsInNLA MI13/TR04, Apache2 attribution retained.
Copyright (c) 2026 George Stepaniants. New formalization by Codex. -/
public import NLA.TR04.OptimalityEquality.CountDefinitions
public import Mathlib.Algebra.Group.Fin.Basic
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.IndexDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix BigOperators

end
end Reference.LexOrderedCyclicBoundary