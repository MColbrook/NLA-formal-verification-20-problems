module

public import NLA.RA02.PaperLUUpperDefinitions
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Infimum of actual squared Frobenius errors over complex rectangular
matrices of rank at most r. No spectral approximation theorem is assumed. -/
def rectangularBestRankErrorSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e}

end NLA.RA02.Paper
