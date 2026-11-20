module

public import NLA.IV04.PaperSignedOrderDefinitions
public import NLA.IV04.PaperWordAdderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def signedZeroFlag (word : List Bool) : List Bool :=
  Complexity.andBit (polynomialSignedLe word [false]) (polynomialSignedLe [false] word)

def tridiagonalBandFlag (row column : List Bool) : List Bool :=
  Complexity.andBit (polynomialWordLe row (polynomialWordAdd column [true]))
    (polynomialWordLe column (polynomialWordAdd row [true]))

/-- Both endpoints must vanish off-band, including the unselected endpoint. -/
def tridiagonalEndpointFlag (row column lower upper : List Bool) : List Bool :=
  Complexity.caseBit₀ (tridiagonalBandFlag row column) [true]
    (Complexity.andBit (signedZeroFlag lower) (signedZeroFlag upper))

def encodedTridiagonalEndpointFlag (input : List Bool) : List Bool :=
  tridiagonalEndpointFlag (Complexity.pairFst input)
    (Complexity.pairFst (Complexity.pairSnd input))
    (Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd input)))
    (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd input)))

end IV04.Paper.Computational
