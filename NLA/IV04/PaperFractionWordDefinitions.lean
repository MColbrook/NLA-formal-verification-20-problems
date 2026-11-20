module

public import NLA.IV04.PaperSignedWordDefinitions
public import Mathlib.Data.Rat.Defs

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Rational meaning of a signed numerator paired with binary denominator bits. -/
def fractionWordValue (input : List Bool) : ℚ :=
  (signedWordValue (Complexity.pairFst input) : ℚ)/
    (wordValue (Complexity.pairSnd input) : ℚ)

/-- Give every input a positive denominator, preserving even the /0 meaning. -/
def normalizeFractionWord (input : List Bool) : List Bool :=
  let denominator := canonicalWord (Complexity.pairSnd input)
  Complexity.caseBit₀ (Complexity.nonemptyFlag denominator)
    (Complexity.pair (Complexity.pairFst input) denominator)
    (Complexity.pair [false] [true])

/-- Exact rational addition, without assuming a polynomial-time arithmetic oracle. -/
def polynomialFractionAdd (left right : List Bool) : List Bool :=
  let l := normalizeFractionWord left
  let r := normalizeFractionWord right
  let ln := Complexity.pairFst l
  let rn := Complexity.pairFst r
  let ld := Complexity.pairSnd l
  let rd := Complexity.pairSnd r
  Complexity.pair
    (polynomialSignedAdd (polynomialSignedMultiply ln (false :: rd))
      (polynomialSignedMultiply rn (false :: ld)))
    (polynomialWordMultiply ld rd)

def polynomialFractionMultiply (left right : List Bool) : List Bool :=
  let l := normalizeFractionWord left
  let r := normalizeFractionWord right
  Complexity.pair
    (polynomialSignedMultiply (Complexity.pairFst l) (Complexity.pairFst r))
    (polynomialWordMultiply (Complexity.pairSnd l) (Complexity.pairSnd r))

def encodedPolynomialFractionAdd (input : List Bool) : List Bool :=
  polynomialFractionAdd (Complexity.pairFst input) (Complexity.pairSnd input)

def encodedPolynomialFractionMultiply (input : List Bool) : List Bool :=
  polynomialFractionMultiply (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
