module

public import NLA.IV04.PaperFractionWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Exclude signed zero when testing negativity. -/
def signedNegativeFlag (bits : List Bool) : List Bool :=
  Complexity.caseBit₀ (Complexity.andBit (Complexity.bitAt [] bits)
    (Complexity.nonemptyFlag (canonicalWord bits.tail))) [true] [false]

def polynomialSignedLe (left right : List Bool) : List Bool :=
  let a := signedNegativeFlag left
  let b := signedNegativeFlag right
  Complexity.caseBit₀ (xorFlag a b) a
    (Complexity.caseBit₀ a (polynomialWordLe right.tail left.tail)
      (polynomialWordLe left.tail right.tail))

def encodedPolynomialSignedLe (input : List Bool) : List Bool :=
  polynomialSignedLe (Complexity.pairFst input) (Complexity.pairSnd input)

/-- Cross multiply only after obtaining positive denominators. -/
def polynomialFractionLe (left right : List Bool) : List Bool :=
  let l := normalizeFractionWord left
  let r := normalizeFractionWord right
  polynomialSignedLe
    (polynomialSignedMultiply (Complexity.pairFst l) (false :: Complexity.pairSnd r))
    (polynomialSignedMultiply (Complexity.pairFst r) (false :: Complexity.pairSnd l))

def encodedPolynomialFractionLe (input : List Bool) : List Bool :=
  polynomialFractionLe (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
