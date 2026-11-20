module

public import NLA.IV04.PaperPayloadLookupDefinitions
public import NLA.IV04.PaperIntegerContinuantMachineDefinitions
public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperWordAdderDefinitions
public import NLA.IV04.PaperWordComparisonDefinitions
public import NLA.IV04.PaperPayloadReverseDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- The dense table is row-major; all addresses are actual binary words. -/
def rowProjectionDiagonalIndex (dimension row : List Bool) : List Bool :=
  canonicalWord (polynomialWordAdd (canonicalWordMultiply row dimension) row)

def rowProjectionLowerIndex (dimension row : List Bool) : List Bool :=
  canonicalWord (polynomialWordAdd (canonicalWordMultiply row dimension) (decrementCount row))

def rowProjectionPreviousUpperIndex (dimension row : List Bool) : List Bool :=
  canonicalWord (polynomialWordAdd (canonicalWordMultiply (decrementCount row) dimension) row)

/-- A continuant row stores the diagonal and its two preceding-row couplings. -/
def rowProjectionRow (dimension row fields : List Bool) : List Bool :=
  let diagonal := polynomialPayloadLookup (Complexity.pair (rowProjectionDiagonalIndex dimension row) fields)
  let lower := Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord row))
    (polynomialPayloadLookup (Complexity.pair (rowProjectionLowerIndex dimension row) fields)) [false]
  let upper := Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord row))
    (polynomialPayloadLookup (Complexity.pair (rowProjectionPreviousUpperIndex dimension row) fields)) [false]
  integerContinuantRow diagonal lower upper

def rowProjectionPack (dimension row fields output : List Bool) : List Bool :=
  Complexity.pair dimension (Complexity.pair row (Complexity.pair fields output))

def rowProjectionStep (state : List Bool) : List Bool :=
  let dimension := Complexity.pairFst state
  let row := Complexity.pairFst (Complexity.pairSnd state)
  let fields := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
  let output := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))
  Complexity.caseBit₀ (polynomialWordLe dimension row)
    (rowProjectionPack dimension row fields output)
    (rowProjectionPack dimension (canonicalWord (polynomialWordAdd row [true])) fields
      (Complexity.pair (rowProjectionRow dimension row fields) output))

def rowProjectionInitial (input : List Bool) : List Bool :=
  rowProjectionPack (canonicalWord (Complexity.pairFst input)) [] (Complexity.pairSnd input) []

/-- Physical input length bounds the number of row iterations, even on malformed data. -/
def rowProjectionState (input : List Bool) : List Bool :=
  (rowProjectionStep^[input.length]) (rowProjectionInitial input)

def polynomialDenseContinuantRows (input : List Bool) : List Bool :=
  let state := rowProjectionState input
  polynomialPayloadReverse (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state)))

end IV04.Paper.Computational
