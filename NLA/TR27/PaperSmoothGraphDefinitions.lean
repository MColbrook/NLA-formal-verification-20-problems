module

public import NLA.TR27.PaperProjectiveChartDefinitions
public import NLA.TR27.PaperHomogeneousDefinitions
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

/-- The whole projective zero set of the actual homogeneous image ideal,
in the certified quotient coordinates. -/
def coordinateImagePoints (D r : ℕ) (hD : 2 ≤ D) : Set (ℙ ℂ (Fin D → ℂ)) :=
  {p | p.rep ∈ MvPolynomial.zeroLocus ℂ (imageIdeal D r hD)}

/-- Explicit smooth-curve geometry: in an actual standard affine chart, the
WHOLE set near p is the graph of analytic functions of one free coordinate.
The neighborhood uses the usual ambient projective quotient topology. -/
def HasProjectiveAnalyticGraph {n : ℕ} (X : Set (ℙ ℂ (Fin n → ℂ))) (p : ℙ ℂ (Fin n → ℂ)) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ p.rep i ≠ 0 ∧
    ∃ V : Set ℂ, ∃ W : Set (ℙ ℂ (Fin n → ℂ)), ∃ H : ℂ → ℙ ℂ (Fin n → ℂ),
      IsOpen V ∧ projectiveCoordinateRatio i j p ∈ V ∧ IsOpen W ∧ p ∈ W ∧
      X ∩ W = H '' V ∧ H (projectiveCoordinateRatio i j p) = p ∧
      (∀ z ∈ V, (H z).rep i ≠ 0 ∧ projectiveCoordinateRatio i j (H z) = z) ∧
      (∀ k, AnalyticOnNhd ℂ (fun z => projectiveCoordinateRatio i k (H z)) V)

end NLA.TR27.Paper
