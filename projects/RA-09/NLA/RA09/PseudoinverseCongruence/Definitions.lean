module

public import NLA.RA09.PaperHarmonicDefinitions
public import NLA.RA09.ComplexHarmonicDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder ComplexOrder
namespace RootRA09PseudoinverseCongruence

def inverseSqrt {n : ℕ} (A : NLA.RA09.RealMatrix n) : NLA.RA09.RealMatrix n :=
  CFC.sqrt (NLA.RA09.spectralPseudoinverse A)

def supportProjector {n : ℕ} (A : NLA.RA09.RealMatrix n) : NLA.RA09.RealMatrix n :=
  A*NLA.RA09.spectralPseudoinverse A

def complexInverseSqrt {n : ℕ} (A : NLA.RA09.ComplexPaper.ComplexMatrix n) : NLA.RA09.ComplexPaper.ComplexMatrix n :=
  CFC.sqrt (NLA.RA09.ComplexPaper.spectralPseudoinverse A)

def complexSupportProjector {n : ℕ} (A : NLA.RA09.ComplexPaper.ComplexMatrix n) : NLA.RA09.ComplexPaper.ComplexMatrix n :=
  A*NLA.RA09.ComplexPaper.spectralPseudoinverse A

def complexOuterSquare {n : ℕ} (v : Fin n → ℂ) : NLA.RA09.ComplexPaper.ComplexMatrix n :=
  Matrix.vecMulVec v (star v)

end RootRA09PseudoinverseCongruence
