module

public import NLA.RA02.PaperInterpolationDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

def interpolatoryResidual {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  A - A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id

def paperTrace {n s : ℕ} (rows : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  (interpolatoryResidual (sharpFamily n t) rows rows).trace

def paperFrobeniusSquared {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (interpolatoryResidual (sharpFamily n t) rows cols i j)^2

end NLA.RA02.Paper
