module

public import NLA.IV04.PaperCountedMachineDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- A bounded scan selects one actual payload field by its binary index. -/
def payloadLookupStep (state : List Bool) : List Bool :=
  let count := Complexity.pairFst state
  let fields := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord count))
    (Complexity.pair (decrementCount count) (Complexity.pairSnd fields))
    (Complexity.pair count fields)

def payloadLookupState (input : List Bool) : List Bool :=
  (payloadLookupStep^[input.length]) (Complexity.pair (Complexity.pairFst input) (Complexity.pairSnd input))

def polynomialPayloadLookup (input : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (payloadLookupState input))

end IV04.Paper.Computational
