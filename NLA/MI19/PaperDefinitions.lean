module

public import NLA.MI19.Definitions
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MI19.Paper

def realWitness : Matrix (Fin 4) (Fin 4) ℝ :=
  !![170,1,167,170; 1,1,-2,1; 167,-2,173,167; 170,1,167,170]

end NLA.MI19.Paper
