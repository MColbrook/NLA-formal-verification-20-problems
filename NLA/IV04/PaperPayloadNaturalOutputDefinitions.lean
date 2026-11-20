module

public import NLA.IV04.PaperCanonicalWordDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Consume one nested binary payload and append its canonical natural code. -/
def payloadNaturalOutputStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let output := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (output ++ canonicalWordCode (Complexity.pairFst rest))) state

/-- Physical input length clocks the program on every bit string. -/
def payloadNaturalOutputState (input : List Bool) : List Bool :=
  (payloadNaturalOutputStep^[input.length]) (Complexity.pair input [])

def polynomialPayloadNaturals (input : List Bool) : List Bool :=
  Complexity.pairSnd (payloadNaturalOutputState input)

end IV04.Paper.Computational
