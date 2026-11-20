module

public import NLA.RA02.PaperSharpDefinitions
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

def rationalLower (n : ℕ) (t : ℚ) : Matrix (Fin n) (Fin n) ℚ := fun i j =>
  if i = j then 1 else if j < i then t^(j.val+1)/(i.val+j.val+2 : ℕ) else 0

def rationalDiagonalScales (n : ℕ) (t : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal (fun i => (t^(n^2))^i.val)

def rationalSharpFamily (n : ℕ) (t : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  rationalLower n t * rationalDiagonalScales n t * (rationalLower n t).transpose

end NLA.RA02.Paper
