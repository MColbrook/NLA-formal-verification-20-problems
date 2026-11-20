module

public import NLA.RA08.PaperNuclearPolarDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearBlockUnitary {m : ℕ} (R : RealMatrix m) : RealMatrix (m+m) :=
  (Matrix.fromBlocks (0 : RealMatrix m) R R.transpose (0 : RealMatrix m)).submatrix
    (finSumFinEquiv (m := m) (n := m)).symm
    (finSumFinEquiv (m := m) (n := m)).symm

end NLA.RA08.Paper
