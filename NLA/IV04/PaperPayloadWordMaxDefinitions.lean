module

public import NLA.IV04.PaperWordComparisonDefinitions
public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Choose one actual binary word by the concrete numeric comparison program. -/
def polynomialWordMax (left right : List Bool) : List Bool :=
  Complexity.caseBit₀ (polynomialWordLe left right) right left

/-- Consume one nested payload, retaining the largest selected binary value. -/
def payloadWordMaxStep (select : List Bool → List Bool) (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let maximum := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (polynomialWordMax maximum (select (Complexity.pairFst rest)))) state

def payloadWordMaxState (select : List Bool → List Bool) (input : List Bool) : List Bool :=
  ((payloadWordMaxStep select)^[input.length]) (Complexity.pair input [])

def polynomialPayloadWordMax (select : List Bool → List Bool) (input : List Bool) : List Bool :=
  canonicalWord (Complexity.pairSnd (payloadWordMaxState select input))

end IV04.Paper.Computational
