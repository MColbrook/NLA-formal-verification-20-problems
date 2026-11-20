module

public import NLA.RA08.PaperNuclearDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace NLA.RA08.Paper.LiteralJoins

def symmetricDilation {m : ℕ} (A : RealMatrix m) : RealMatrix (m+m) :=
  (Matrix.fromBlocks 0 A A.transpose 0).submatrix
    (finSumFinEquiv (m := m) (n := m)).symm (finSumFinEquiv (m := m) (n := m)).symm

def blockDiagonal {m : ℕ} (U V : RealMatrix m) : RealMatrix (m+m) :=
  (Matrix.fromBlocks U 0 0 V).submatrix
    (finSumFinEquiv (m := m) (n := m)).symm (finSumFinEquiv (m := m) (n := m)).symm

def repeatedEntries {m : ℕ} (s : Fin m → ℝ) : Fin (m+m) → ℝ :=
  fun i => Sum.elim s s ((finSumFinEquiv (m := m) (n := m)).symm i)

end NLA.RA08.Paper.LiteralJoins
