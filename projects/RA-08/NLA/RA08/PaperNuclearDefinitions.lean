module

public import NLA.RA08.PaperDerivativeDefinitions
public import Mathlib.Data.Matrix.Block

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace NLA.RA08.Paper

/-- The actual nuclear norm: the trace of the positive square root of AᵀA. -/
def nuclearNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (functionalCalculus Real.sqrt (A.transpose*A)).trace

def nuclearHeight {m : ℕ} (i : Fin m) : ℝ := (1/4 : ℝ)^(i.val+1)

def nuclearBaseEntries (m : ℕ) : Fin (m+m) → ℝ :=
  fun i => Sum.elim (fun j => 1-nuclearHeight j) (fun j => 1+nuclearHeight j)
    ((finSumFinEquiv (m := m) (n := m)).symm i)

def nuclearBase (m : ℕ) : RealMatrix (m+m) := Matrix.diagonal (nuclearBaseEntries m)

def nuclearUnitVector (m : ℕ) : Fin (m+m) → ℝ := fun _ => (Real.sqrt (2*m : ℝ))⁻¹

def nuclearPerturbation (m : ℕ) : RealMatrix (m+m) :=
  fun i j => nuclearUnitVector m i*nuclearUnitVector m j

/-- The actual derivative, rather than an assumed or numerically supplied matrix. -/
def nuclearDerivative (m : ℕ) : RealMatrix (m+m) :=
  clippingDerivative (nuclearBaseEntries m) (nuclearPerturbation m)

def nuclearKernel (m : ℕ) : RealMatrix m :=
  fun i j => nuclearHeight i/(nuclearHeight i+nuclearHeight j)

def nuclearTriangular (m : ℕ) : RealMatrix m := fun i j => if i ≤ j then 1 else 0

/-- The printed block expression, whose equality with the actual derivative is
    a separate proof obligation. Indices are reordered by the standard finite sum. -/
def nuclearDisplayedDerivative (m : ℕ) : RealMatrix (m+m) :=
  (1/(2*m) : ℝ) •
    (Matrix.fromBlocks (fun (_ _ : Fin m) => (1 : ℝ)) (nuclearKernel m)
      (nuclearKernel m).transpose (0 : RealMatrix m)).submatrix
      (finSumFinEquiv (m := m) (n := m)).symm
      (finSumFinEquiv (m := m) (n := m)).symm

end NLA.RA08.Paper
