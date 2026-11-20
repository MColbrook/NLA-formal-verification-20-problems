module

public import NLA.RA02.PaperTailDefinitions
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Infimum of actual squared Frobenius errors over all complex matrices of
rank at most r. Attainment and its spectral value are proved separately. -/
def bestRankErrorSquared {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ B : NLA.RA02.Square n, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e}

end NLA.RA02.Paper
