module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Normed.Ring.Units

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex
open scoped Real
namespace NLA.RA08.Paper.LiteralContour
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def contourResolvent (B : A) (z : ℂ) : A := Ring.inverse (z • (1 : A)-B)

def contourClipping (B : A) (c : ℂ) (r : ℝ) : A :=
  B-(2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), (z-1) • contourResolvent B z

def contourClippingDerivative (B E : A) (c : ℂ) (r : ℝ) : A :=
  E-(2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r),
    (z-1) • (contourResolvent B z*E*contourResolvent B z)

end NLA.RA08.Paper.LiteralContour
