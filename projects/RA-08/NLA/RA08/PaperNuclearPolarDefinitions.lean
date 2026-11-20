module

public import NLA.RA08.PaperNuclearTriangularDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearTriangularGram (m : ℕ) : RealMatrix m :=
  (nuclearTriangular m).transpose*nuclearTriangular m

/-- The polar matrix of the actual invertible triangular matrix. -/
def nuclearTriangularPolar (m : ℕ) : RealMatrix m :=
  nuclearTriangular m*functionalCalculus (fun x : ℝ => (Real.sqrt x)⁻¹)
    (nuclearTriangularGram m)

end NLA.RA08.Paper
