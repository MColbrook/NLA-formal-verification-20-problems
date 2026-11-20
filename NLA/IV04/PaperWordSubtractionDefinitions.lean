module

public import NLA.IV04.PaperWordComparisonDefinitions
public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Two's-complement subtraction at a width computed from input lengths. -/
def rawWordDifference (left right : List Bool) : List Bool :=
  let ruler := false :: (left ++ right)
  (polynomialWordAdd left
    (polynomialWordAdd [true] ((Complexity.padTo ruler right).map Bool.not))).take ruler.length

/-- Saturating natural subtraction, on binary words, with no value-indexed loop. -/
def polynomialWordSub (left right : List Bool) : List Bool :=
  Complexity.caseBit₀ (polynomialWordLe right left) (rawWordDifference left right) []

def encodedPolynomialWordSub (input : List Bool) : List Bool :=
  polynomialWordSub (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
