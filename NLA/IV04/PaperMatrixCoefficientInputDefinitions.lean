module

public import NLA.IV04.PaperNaturalParserDefinitions
public import NLA.IV04.PaperFractionCoefficientDefinitions
public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperWordAdderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Both dense endpoints contain n² rational fields, followed by one threshold. -/
def matrixFieldCountWord (dimension : List Bool) : List Bool :=
  canonicalWord (polynomialWordAdd (false :: canonicalWordMultiply dimension dimension) [true])

def matrixDimensionWord (input : List Bool) : List Bool :=
  canonicalWord (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input)))

def matrixRationalFieldInput (input : List Bool) : List Bool :=
  let parsed := encodedNaturalParser input
  Complexity.pair (matrixFieldCountWord (Complexity.pairFst (Complexity.pairSnd parsed)))
    (Complexity.pairSnd (Complexity.pairSnd parsed))

/-- Actual bit program: header validity, dimension, denominator, integer fields, unused tail. -/
def encodedMatrixCoefficientInput (input : List Bool) : List Bool :=
  let header := encodedNaturalParser input
  let cleared := encodedRationalListClearing (matrixRationalFieldInput input)
  Complexity.pair (Complexity.andBit (Complexity.pairFst header) (Complexity.pairFst cleared))
    (Complexity.pair (matrixDimensionWord input) (Complexity.pairSnd cleared))

/-- Semantic reference to the manuscript's natural and rational decoders. -/
def readMatrixRationals (input : List Bool) : Option (ℕ × List ℚ × List Bool) := do
  let (n,rest) ← IV04.Paper.readNatural input
  let (values,tail) ← readRationals (2*n*n+1) rest
  return (n,values,tail)

end IV04.Paper.Computational
