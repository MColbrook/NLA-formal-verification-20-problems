module

public import NLA.IV04.PaperDenseContinuantDeterminantDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- The literal row-major matrix represented by the signed words and common denominator. -/
def denseWordRationalMatrix (n D : ℕ) (words : List (List Bool)) : RatMat n :=
  fun i j => (signedWordValue (words.getD (i.val*n+j.val) []) : ℚ)/(D : ℚ)

end IV04.Paper.Computational