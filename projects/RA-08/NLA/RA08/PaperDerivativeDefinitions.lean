module

public import NLA.RA08.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA08.Paper

/-- The printed divided difference, including both diagonal cases away from one. -/
def clippingDividedDifference (x y : ℝ) : ℝ :=
  if x = y then (if x < 1 then 1 else 0)
  else (witnessFunction x-witnessFunction y)/(x-y)

def clippingDerivative {n : ℕ} (b : Fin n → ℝ) (E : RealMatrix n) : RealMatrix n :=
  fun i j => clippingDividedDifference (b i) (b j)*E i j

def matrixAbsolute {n : ℕ} (A : RealMatrix n) : RealMatrix n := functionalCalculus abs A

def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

open scoped Matrix.Norms.Frobenius in
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖

def diagonalSylvesterInverse {n : ℕ} (a : Fin n → ℝ) (F : RealMatrix n) : RealMatrix n :=
  fun i j => F i j/(a i+a j)

end NLA.RA08.Paper
