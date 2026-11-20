module

public import NLA.MD06.GraphCriticalityHessian.LiftDefinitions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open scoped BigOperators
abbrev Configuration (n : ℕ) := EuclideanSpace ℝ (Fin n)
def CorrectionBall (n : ℕ) (rho : ℝ) : Set (Configuration n) :=
  {h | (∑ i, h i) = 0 ∧ ‖h‖ ≤ rho}
def LiftedEnergy {n : ℕ} (G : SimpleGraph (Fin n)) (phi : Configuration n) : ℝ :=
  Reference.MD06Actual.RealEnergy G (fun i => phi i)
end Reference.MD06Correction
