module

public import NLA.MF05.PaperNormDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

def complexRotated {d : ℕ} (Q : NLA.MF07.Square d) (σ : Fin d → ℝ) (A : NLA.MF07.Square d) :
    NLA.MF07.Square d :=
  (NLA.MF07.diagonalWeights σ)⁻¹ * Q.conjTranspose * A * Q * NLA.MF07.diagonalWeights σ

def realRotated {d : ℕ} (Q : RealSquare d) (σ : Fin d → ℝ) (A : RealSquare d) : RealSquare d :=
  (Matrix.diagonal σ)⁻¹ * Q.transpose * A * Q * Matrix.diagonal σ

end NLA.MF05.Paper
