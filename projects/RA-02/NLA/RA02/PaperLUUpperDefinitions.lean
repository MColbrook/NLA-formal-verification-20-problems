module

public import NLA.RA02.Definitions
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

/-- The actual ordered-eigenvalue tail of the complex Gram matrix. -/
def gramTail {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) : ℝ :=
  NLA.RA02.rankTail (A.conjTranspose*A) (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian r

end NLA.RA02.Paper
