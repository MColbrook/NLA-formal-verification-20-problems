module

public import NLA.RA02.PaperSharpDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Continuous extension of epsilon^r times the inverse printed family. -/
def scaledFamilyInverse (r : ℕ) (t : ℝ) : Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  ((lower (r+1) t)⁻¹).transpose * Matrix.diagonal (fun i => epsilon (r+1) t^(r-i.val)) *
    (lower (r+1) t)⁻¹

def lastCoordinateProjection (r : ℕ) : Matrix (Fin (r+1)) (Fin (r+1)) ℝ :=
  Matrix.diagonal (Pi.single (Fin.last r) 1)

end NLA.RA02.Paper
