module

public import NLA.IV04.PaperCanonicalWordDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Count nested payload fields by actual binary increment, ignoring their contents. -/
def payloadCountStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let count := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest) (polynomialWordAdd count [true])) state

def payloadCountState (input : List Bool) : List Bool :=
  (payloadCountStep^[input.length]) (Complexity.pair input [])

def polynomialPayloadCount (input : List Bool) : List Bool :=
  canonicalWord (Complexity.pairSnd (payloadCountState input))

end IV04.Paper.Computational
