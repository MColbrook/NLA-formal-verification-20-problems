module

public import NLA.IV04.PaperPayloadCountDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Sum the actual field counts of each nested payload by binary addition. -/
def nestedPayloadCountStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let total := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (polynomialWordAdd total (polynomialPayloadCount (Complexity.pairFst rest)))) state

def nestedPayloadCountState (input : List Bool) : List Bool :=
  (nestedPayloadCountStep^[input.length]) (Complexity.pair input [])

def polynomialNestedPayloadCount (input : List Bool) : List Bool :=
  canonicalWord (Complexity.pairSnd (nestedPayloadCountState input))

end IV04.Paper.Computational
