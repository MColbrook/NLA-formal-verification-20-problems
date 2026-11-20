module

public import NLA.IV04.PaperCountedMachineDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions
public import NLA.IV04.PaperSignedOrderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def vertexSelectionPack (count flag fields choices output : List Bool) : List Bool :=
  Complexity.pair count (Complexity.pair flag (Complexity.pair fields (Complexity.pair choices output)))

def vertexSelectionCount (state : List Bool) : List Bool := Complexity.pairFst state
def vertexSelectionFlag (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd state)
def vertexSelectionFields (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
def vertexSelectionChoices (state : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state)))
def vertexSelectionOutput (state : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state)))

def vertexSelectionReady (fields choices : List Bool) : List Bool :=
  Complexity.andBit (Complexity.nonemptyFlag fields)
    (Complexity.andBit (Complexity.nonemptyFlag (Complexity.pairSnd fields))
      (Complexity.andBit (Complexity.nonemptyFlag choices)
        (polynomialSignedLe (Complexity.pairFst fields) (Complexity.pairFst (Complexity.pairSnd fields)))))

def vertexSelectedWord (fields choices : List Bool) : List Bool :=
  Complexity.caseBit₀ choices (Complexity.pairFst (Complexity.pairSnd fields)) (Complexity.pairFst fields)

def vertexSelectionStep (state : List Bool) : List Bool :=
  let count := vertexSelectionCount state
  let flag := vertexSelectionFlag state
  let fields := vertexSelectionFields state
  let choices := vertexSelectionChoices state
  let output := vertexSelectionOutput state
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord count))
    (Complexity.caseBit₀ flag
      (Complexity.caseBit₀ (vertexSelectionReady fields choices)
        (vertexSelectionPack (decrementCount count) [true]
          (Complexity.pairSnd (Complexity.pairSnd fields)) choices.tail
          (Complexity.pair (vertexSelectedWord fields choices) output))
        (vertexSelectionPack count [false] fields choices output)) state) state

/-- Input contains a binary count, the flattened lower/upper coefficient table and choice bits. -/
def vertexSelectionInitial (input : List Bool) : List Bool :=
  vertexSelectionPack (canonicalWord (Complexity.pairFst input)) [true]
    (Complexity.pairFst (Complexity.pairSnd input)) (Complexity.pairSnd (Complexity.pairSnd input)) []

def vertexSelectionState (input : List Bool) : List Bool :=
  (vertexSelectionStep^[input.length]) (vertexSelectionInitial input)

/-- Preserve unused fields and choices, so the complete verifier can reject extra certificate bits. -/
def encodedVertexSelection (input : List Bool) : List Bool :=
  let state := vertexSelectionState input
  Complexity.pair
    (Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord (vertexSelectionCount state)))
      [false] (vertexSelectionFlag state))
    (Complexity.pair (vertexSelectionOutput state)
      (Complexity.pair (vertexSelectionFields state) (vertexSelectionChoices state)))

end IV04.Paper.Computational
