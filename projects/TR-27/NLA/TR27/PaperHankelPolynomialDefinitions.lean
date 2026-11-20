module

public import NLA.TR27.PaperGeneralHankelDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

def hankelPolynomialMatrix {D : ℕ} (n : ℕ) (hD : 2*n ≤ D) :
    Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Fin (D+1)) ℂ) :=
  Matrix.of (fun i j => MvPolynomial.X (⟨i.val+j.val, by omega⟩ : Fin (D+1)))

/-- The actual determinant polynomial in the source homogeneous coordinates. -/
def hankelPolynomial {D : ℕ} (n : ℕ) (hD : 2*n ≤ D) : MvPolynomial (Fin (D+1)) ℂ :=
  (hankelPolynomialMatrix n hD).det

end NLA.TR27.Paper
