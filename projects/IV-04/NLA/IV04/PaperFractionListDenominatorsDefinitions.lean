module

public import NLA.IV04.PaperWordListProductDefinitions
public import NLA.IV04.PaperRationalListParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def fractionListDenominatorsStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let output := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (Complexity.pair (Complexity.pairSnd (Complexity.pairFst rest)) output)) state

def fractionListDenominatorsState (input : List Bool) : List Bool :=
  (fractionListDenominatorsStep^[input.length]) (Complexity.pair input [])

/-- A reversed nested list of the denominator words. -/
def polynomialFractionListDenominators (input : List Bool) : List Bool :=
  Complexity.pairSnd (fractionListDenominatorsState input)

/-- Compute a normalized common denominator from the actual parsed fraction words. -/
def polynomialRationalListDenominator (input : List Bool) : List Bool :=
  canonicalWord (polynomialWordListProduct (polynomialFractionListDenominators
    (Complexity.pairFst (Complexity.pairSnd (encodedRationalListParser input)))))

end IV04.Paper.Computational
