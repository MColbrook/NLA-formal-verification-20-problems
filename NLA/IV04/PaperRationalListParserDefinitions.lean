module

public import NLA.IV04.PaperRationalParserDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Semantic reference; the requested count is a natural value, not a runtime certificate. -/
def readRationals : ℕ → List Bool → Option (List ℚ × List Bool)
  | 0, input => some ([],input)
  | count+1, input => do
      let (value,tail) ← IV04.Paper.readRational input
      let (values,last) ← readRationals count tail
      return (value :: values,last)

def fuelReadRationals : ℕ → ℕ → List Bool → Option (List ℚ × List Bool)
  | _, 0, input => some ([],input)
  | 0, _+1, _ => none
  | fuel+1, count+1, input => do
      let (value,tail) ← IV04.Paper.readRational input
      let (values,last) ← fuelReadRationals fuel count tail
      return (value :: values,last)

/-- One rational field at a time, preserving a reversed list of normalized fraction words. -/
def rationalListStep (state : List Bool) : List Bool :=
  let count := countedCount state
  let flag := countedFlag state
  let rest := countedRest state
  let output := countedOutput state
  let parsed := encodedRationalParser rest
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord count))
    (Complexity.caseBit₀ flag
      (Complexity.caseBit₀ (Complexity.pairFst parsed)
        (countedPack (decrementCount count) [true]
          (Complexity.pairSnd (Complexity.pairSnd parsed))
          (Complexity.pair (Complexity.pairFst (Complexity.pairSnd parsed)) output))
        (countedPack count [false] rest output)) state) state

/-- Input is a pair of a binary count and the rational-code stream. -/
def rationalListInitial (input : List Bool) : List Bool :=
  countedPack (canonicalWord (Complexity.pairFst input)) [true] (Complexity.pairSnd input) []

/-- Always clocked by the physical input length, including malformed and huge counts. -/
def rationalListState (input : List Bool) : List Bool :=
  (rationalListStep^[input.length]) (rationalListInitial input)

def encodedRationalListParser (input : List Bool) : List Bool :=
  let state := rationalListState input
  Complexity.pair
    (Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord (countedCount state)))
      [false] (countedFlag state))
    (Complexity.pair (countedOutput state) (countedRest state))

/-- Semantic interpretation only; genuine machine FP is proved for the concrete bit program. -/
def decodeFractionPayloads : ℕ → List Bool → List ℚ
  | 0, _ => []
  | fuel+1, input => if input=[] then [] else
      fractionWordValue (Complexity.pairFst input) :: decodeFractionPayloads fuel (Complexity.pairSnd input)

def rationalListParserResult (input : List Bool) : Option (List ℚ × List Bool) :=
  let parsed := encodedRationalListParser input
  if Complexity.pairFst parsed=[true] then
    let output := Complexity.pairFst (Complexity.pairSnd parsed)
    some ((decodeFractionPayloads output.length output).reverse,Complexity.pairSnd (Complexity.pairSnd parsed))
  else none

end IV04.Paper.Computational
