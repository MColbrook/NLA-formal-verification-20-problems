module

public import NLA.RA08.PaperNuclearTailDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix
namespace NLA.RA08.Paper.LiteralContour

def smallTailBlock (m : ℕ) (η t : ℝ) : RealMatrix (m+m) :=
  nuclearBase m+(t*η) • nuclearPerturbation m-nuclearLiftSmallest m η t • 1

def distanceError (d : ℕ) : ℝ :=
  if d=0 then 0 else ((1/4 : ℝ)^d/(1+(1/4 : ℝ)^d))^2

def nuclearBlockSign (m : ℕ) : RealMatrix (m+m) :=
  diagonal (fun i => Sum.elim (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin m => -1)
    ((finSumFinEquiv (m := m) (n := m)).symm i))

def nuclearOffDiagonal (m : ℕ) : RealMatrix (m+m) :=
  (1/(2*m) : ℝ) •
    (Matrix.fromBlocks (0 : RealMatrix m) (nuclearKernel m)
      (nuclearKernel m).transpose (0 : RealMatrix m)).submatrix
      (finSumFinEquiv (m := m) (n := m)).symm
      (finSumFinEquiv (m := m) (n := m)).symm

end NLA.RA08.Paper.LiteralContour
