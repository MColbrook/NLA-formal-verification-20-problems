module

public import NLA.RA08.PaperNuclearLiftDerivativeDefinitions
public import NLA.RA08.PaperNuclearSignDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftUnitary {n : ℕ} (R : RealMatrix n) : RealMatrix (n+1) :=
  (Matrix.fromBlocks R 0 0 (1 : RealMatrix 1)).submatrix
    (finSumFinEquiv (m := n) (n := 1)).symm
    (finSumFinEquiv (m := n) (n := 1)).symm

end NLA.RA08.Paper
