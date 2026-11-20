module

public import NLA.IV04.PaperNaturalParserDefinitions
public import NLA.IV04.PaperFractionWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def rationalParserFirst (input : List Bool) := encodedNaturalParser input.tail
def rationalParserSecond (input : List Bool) :=
  encodedNaturalParser (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input)))

def rationalParserFlag (input : List Bool) : List Bool :=
  Complexity.andBit (Complexity.nonemptyFlag input)
    (Complexity.andBit (Complexity.pairFst (rationalParserFirst input))
      (Complexity.pairFst (rationalParserSecond input)))

def rationalParserFraction (input : List Bool) : List Bool :=
  normalizeFractionWord (Complexity.pair
    (signedWordPack (Complexity.bitAt [] input)
      (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))))
    (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))))

/-- Total rational parser: validity flag, fraction code and unused input. -/
def encodedRationalParser (input : List Bool) : List Bool :=
  Complexity.pair (rationalParserFlag input)
    (Complexity.pair (rationalParserFraction input)
      (Complexity.pairSnd (Complexity.pairSnd (rationalParserSecond input))))

end IV04.Paper.Computational
