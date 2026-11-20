module

public import NLA.IV04.PaperFractionListDenominatorsDefinitions
public import NLA.IV04.PaperSignedWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Denominator product on an already encoded fraction list. -/
def fractionWordListDenominator (input : List Bool) : List Bool :=
  canonicalWord (polynomialWordListProduct (polynomialFractionListDenominators input))

def coefficientPack (rest prior output : List Bool) : List Bool :=
  Complexity.pair rest (Complexity.pair prior output)

def coefficientRest (state : List Bool) : List Bool := Complexity.pairFst state
def coefficientPrefix (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd state)
def coefficientOutput (state : List Bool) : List Bool := Complexity.pairSnd (Complexity.pairSnd state)

/-- Clear one numerator by multiplying the denominators before and after its field. -/
def clearedFractionWord (prior fraction suffix : List Bool) : List Bool :=
  polynomialSignedMultiply (Complexity.pairFst fraction)
    (false :: canonicalWordMultiply prior (fractionWordListDenominator suffix))

def fractionCoefficientStep (state : List Bool) : List Bool :=
  let rest := coefficientRest state
  let prior := coefficientPrefix state
  let output := coefficientOutput state
  let fraction := Complexity.pairFst rest
  let suffix := Complexity.pairSnd rest
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (coefficientPack suffix (canonicalWordMultiply prior (Complexity.pairSnd fraction))
      (Complexity.pair (clearedFractionWord prior fraction suffix) output)) state

def fractionCoefficientInitial (input : List Bool) : List Bool := coefficientPack input [true] []

def fractionCoefficientState (input : List Bool) : List Bool :=
  (fractionCoefficientStep^[input.length]) (fractionCoefficientInitial input)

/-- Reversed nested list of signed integer coefficient words. -/
def polynomialFractionCoefficients (input : List Bool) : List Bool :=
  coefficientOutput (fractionCoefficientState input)

/-- Preserve parser validity and tail alongside the common denominator and cleared coefficients. -/
def encodedRationalListClearing (input : List Bool) : List Bool :=
  let parsed := encodedRationalListParser input
  let fractions := Complexity.pairFst (Complexity.pairSnd parsed)
  Complexity.pair (Complexity.pairFst parsed)
    (Complexity.pair (polynomialRationalListDenominator input)
      (Complexity.pair (polynomialFractionCoefficients fractions)
        (Complexity.pairSnd (Complexity.pairSnd parsed))))

end IV04.Paper.Computational
