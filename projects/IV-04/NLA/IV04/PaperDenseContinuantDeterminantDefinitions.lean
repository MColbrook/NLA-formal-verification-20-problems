module

public import NLA.IV04.PaperDenseContinuantProjectionReference

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def denseWordDiagonal (size : ℕ) (words : List (List Bool)) (i : ℕ) : ℤ :=
  signedWordValue (words.getD (i*size+i) [])

def denseWordLower (size : ℕ) (words : List (List Bool)) (i : ℕ) : ℤ :=
  signedWordValue (words.getD (i*size+(i-1)) [])

def denseWordUpper (size : ℕ) (words : List (List Bool)) (i : ℕ) : ℤ :=
  signedWordValue (words.getD (i*size+(i+1)) [])

/-- Extract the actual tridiagonal rows and run the actual signed continuant program. -/
def polynomialDenseIntegerDeterminant (input : List Bool) : List Bool :=
  polynomialIntegerContinuant (polynomialDenseContinuantRows input)

end IV04.Paper.Computational