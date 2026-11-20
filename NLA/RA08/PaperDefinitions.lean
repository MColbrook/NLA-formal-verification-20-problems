module

public import NLA.RA08.Definitions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/- Proof-independent definitions of the paper's fixed Nyström sketch. -/
set_option autoImplicit false
open Matrix
noncomputable section
namespace NLA.RA08.Paper

def paperOmega : Matrix (Fin 6) (Fin 3) ℝ :=
  !![1,0,0; 0,1,0; 0,0,1; -8/9,-64/9,32/9; -64/9,-8/9,-32/9; 0,0,0]

def nystrom {n l : ℕ} (A : RealMatrix n) (Ω : Matrix (Fin n) (Fin l) ℝ) :
    RealMatrix n := A * Ω * (Ω.transpose * A * Ω)⁻¹ * Ω.transpose * A

end NLA.RA08.Paper
