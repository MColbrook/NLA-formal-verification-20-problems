module

public import NLA.IV04.PaperDenseWordMatrixDefinitions
public import NLA.IV04.PaperVertexSelectionReference
public import NLA.IV04.PaperMatrixDenseSupportReference

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def selectedRationalEndpoints : List (ℚ × ℚ) → List Bool → List ℚ
  | [], _ => []
  | (lower,upper)::rows, choices =>
      (if choices.headD false then upper else lower)::selectedRationalEndpoints rows choices.tail

/-- The literal endpoint-selected rational matrix in row-major order. -/
def rationalEndpointVertex (n : ℕ) (pairs : List (ℚ × ℚ)) (choices : List Bool) : RatMat n :=
  fun i j => (selectedRationalEndpoints pairs choices).getD (i.val*n+j.val) 0

end IV04.Paper.Computational