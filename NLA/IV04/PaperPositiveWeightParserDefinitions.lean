module

public import NLA.IV04.PaperWordListPositiveDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- A counted prefix parser with actual nonempty, strictly positive weight validation. -/
def encodedPositiveWeightParser (input : List Bool) : List Bool :=
  let parsed := encodedCountedNaturalParser input
  let output := Complexity.pairFst (Complexity.pairSnd parsed)
  Complexity.pair
    (Complexity.andBit (Complexity.pairFst parsed) (polynomialNonemptyPositiveWordList output))
    (Complexity.pairSnd parsed)

/-- The interpretation of the concrete parser output, retaining the unused input tail. -/
def positiveWeightParserResult (input : List Bool) : Option (List ℕ × List Bool) :=
  let parsed := encodedPositiveWeightParser input
  if Complexity.pairFst parsed=[true] then
    let output := Complexity.pairFst (Complexity.pairSnd parsed)
    some ((decodePayloads output.length output).reverse,Complexity.pairSnd (Complexity.pairSnd parsed))
  else none

/-- Semantic specification, using the paper's existing counted-weight decoder. -/
def readPositiveIntegerWeights (input : List Bool) : Option (List ℕ × List Bool) := do
  let (weights,tail) ← IV04.Paper.readIntegerWeights input
  if weights ≠ [] ∧ ∀ w ∈ weights, 0 < w then some (weights,tail) else none

/-- Complete-input validity: valid positive weights and no trailing bits. -/
def polynomialPositiveWeightInput (input : List Bool) : List Bool :=
  let parsed := encodedPositiveWeightParser input
  Complexity.andBit (Complexity.pairFst parsed)
    (Complexity.caseBit₀ (Complexity.nonemptyFlag (Complexity.pairSnd (Complexity.pairSnd parsed)))
      [false] [true])

end IV04.Paper.Computational
