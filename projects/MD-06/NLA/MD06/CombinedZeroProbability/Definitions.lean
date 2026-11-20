module

public import NLA.MD06.CombinedDescendingMoments.JointDefinitions
public import NLA.MD06.CubicConfiguration.UniformDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Reference.MD06CombinedMoments Reference.MD06MixedLowCycleBijections
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PartialMoment (k ell t : ℕ) : ℝ :=
  ∑q∈Finset.range (t+1),(-1 : ℝ)^q*(MeanDescending (Size k) q ell/(q.factorial : ℝ))
def PartialExponential (ell t : ℕ) : ℝ :=
  ∑q∈Finset.range (t+1),(-(2+(2 : ℝ)^ell/(2*(ell : ℝ))))^q/(q.factorial : ℝ)
def ZeroProbability (k ell : ℕ) : ℝ :=
  PairingProbability (Size k) (fun p => MarkedMatchingCount (ell:=ell) p=0)
end Reference.MD06CombinedZero
