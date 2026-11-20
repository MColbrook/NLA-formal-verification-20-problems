module

public import NLA.IV04.PaperWordSubtractionDefinitions
public import NLA.IV04.PaperWordMultiplierDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Sign bit followed by a least-significant-first magnitude. -/
def signedWordValue (bits : List Bool) : ℤ :=
  if firstBit bits then -(wordValue bits.tail : ℤ) else (wordValue bits.tail : ℤ)

def signedWordPack (flag magnitude : List Bool) : List Bool :=
  Complexity.caseBit₀ flag (true :: canonicalWord magnitude) (false :: canonicalWord magnitude)

def polynomialSignedNeg (bits : List Bool) : List Bool :=
  signedWordPack (Complexity.notBit (Complexity.bitAt [] bits)) bits.tail

def polynomialSignedAdd (left right : List Bool) : List Bool :=
  let a := Complexity.bitAt [] left
  let b := Complexity.bitAt [] right
  let x := left.tail
  let y := right.tail
  Complexity.caseBit₀ (xorFlag a b)
    (Complexity.caseBit₀ (polynomialWordLe x y)
      (signedWordPack b (polynomialWordSub y x))
      (signedWordPack a (polynomialWordSub x y)))
    (signedWordPack a (polynomialWordAdd x y))

def polynomialSignedMultiply (left right : List Bool) : List Bool :=
  signedWordPack (xorFlag (Complexity.bitAt [] left) (Complexity.bitAt [] right))
    (polynomialWordMultiply left.tail right.tail)

def encodedPolynomialSignedAdd (input : List Bool) : List Bool :=
  polynomialSignedAdd (Complexity.pairFst input) (Complexity.pairSnd input)

def encodedPolynomialSignedMultiply (input : List Bool) : List Bool :=
  polynomialSignedMultiply (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
