module

public import NLA.MI22.Definitions
public import NLA.RA09.LiteralIntegral.Definitions
public import NLA.MI22.LiteralDerivative.Definitions
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MI22.MatrixIntegral

def resolvent {A : Type*} [Ring A] [Algebra ℝ A] (t : ℝ) (a : A) : A :=
  Ring.inverse (algebraMap ℝ A t + a)

def powerKernel {A : Type*} [Ring A] [Algebra ℝ A] (p t : ℝ) (a : A) : A :=
  t^(p-1) • (a * resolvent t a)

def differenceKernel {A : Type*} [Ring A] [Algebra ℝ A] (p t : ℝ) (P Q : A) : A :=
  t^p • (resolvent t Q * (P-Q) * resolvent t P)

end NLA.MI22.MatrixIntegral
