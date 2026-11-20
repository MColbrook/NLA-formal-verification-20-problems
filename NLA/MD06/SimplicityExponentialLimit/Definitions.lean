module

public import NLA.MD06.DisjointTypedEnumeration.MeanDefinitions
public import NLA.MD06.BadJointMoments.OrderDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06SimplicityExponential
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments
open scoped BigOperators

def PartialMoment (k t : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (t+1),(-1 : ℝ)^q*(MeanBadDescending k q/(q.factorial : ℝ))

def PartialPoisson (t : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (t+1),(-2 : ℝ)^q/(q.factorial : ℝ)

def SimpleProbability (k : ℕ) : ℝ :=
  ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal
end Reference.MD06SimplicityExponential
