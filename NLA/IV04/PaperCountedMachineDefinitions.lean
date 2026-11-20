module

public import NLA.IV04.PaperCountedParserDefinitions
public import NLA.IV04.PaperWordSubtractionDefinitions
public import Mathlib.Logic.Function.Iterate

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def countedPack (count flag rest output : List Bool) : List Bool :=
  Complexity.pair count (Complexity.pair flag (Complexity.pair rest output))

def countedCount (state : List Bool) : List Bool := Complexity.pairFst state
def countedFlag (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd state)
def countedRest (state : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
def countedOutput (state : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))

def decrementCount (count : List Bool) : List Bool :=
  canonicalWord (polynomialWordSub count [true])

/-- Consume at most one natural per step, retaining a reversed nested list of raw payloads. -/
def countedStep (state : List Bool) : List Bool :=
  let count := countedCount state
  let flag := countedFlag state
  let rest := countedRest state
  let output := countedOutput state
  let parsed := encodedNaturalParser rest
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord count))
    (Complexity.caseBit₀ flag
      (Complexity.caseBit₀ (Complexity.pairFst parsed)
        (countedPack (decrementCount count) [true]
          (Complexity.pairSnd (Complexity.pairSnd parsed))
          (Complexity.pair (Complexity.pairFst (Complexity.pairSnd parsed)) output))
        (countedPack count [false] rest output)) state) state

def countedInitial (input : List Bool) : List Bool :=
  let parsed := encodedNaturalParser input
  countedPack (canonicalWord (Complexity.pairFst (Complexity.pairSnd parsed)))
    (Complexity.pairFst parsed) (Complexity.pairSnd (Complexity.pairSnd parsed)) []

/-- The clock is actual input length, regardless of the value of the count field. -/
def countedMachineState (input : List Bool) : List Bool :=
  (countedStep^[input.length]) (countedInitial input)

def encodedCountedNaturalParser (input : List Bool) : List Bool :=
  let state := countedMachineState input
  Complexity.pair
    (Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord (countedCount state)))
      [false] (countedFlag state))
    (Complexity.pair (countedOutput state) (countedRest state))

end IV04.Paper.Computational
