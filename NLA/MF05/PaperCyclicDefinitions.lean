module

public import NLA.MF05.PaperRealDefinitions
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/- Literal matrices for the paper's Holder-sharpness example, in dimension n+1. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper.Cyclic

def shift (n : ℕ) : RealSquare (n + 1) := fun i j =>
  if i.val + 1 = j.val then 1 else 0

def corner (n : ℕ) : RealSquare (n + 1) := Matrix.single (Fin.last n) 0 1

def weight (n : ℕ) (δ : ℝ) (i : Fin (n + 1)) : ℝ :=
  if i = Fin.last n then δ else 1

def perturbation (n : ℕ) (δ : ℝ) : RealSquare (n + 1) := fun i j =>
  if j = finRotate (n + 1) i then weight n δ i else 0

def eigenvector (n : ℕ) (r : ℝ) : RealVector (n + 1) :=
  WithLp.toLp 2 (fun i => r ^ i.val)

end NLA.MF05.Paper.Cyclic
