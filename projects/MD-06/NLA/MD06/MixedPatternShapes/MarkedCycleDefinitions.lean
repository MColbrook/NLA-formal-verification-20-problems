module

public import NLA.MD06.MixedPatternShapes.BadCycleDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06Simplicity

def MarkedLength {n ell : ℕ} (d : MarkedDatum n ell) : ℕ :=
  match d with
  | .inl b => BadLength b
  | .inr _ => ell

def MarkedCycle {n ell : ℕ} (d : MarkedDatum n ell) : CycleData n (MarkedLength d) :=
  match d with
  | .inl b => BadCycle b
  | .inr C => Classical.choose C.property

end Reference.MD06MixedPatternShapes
