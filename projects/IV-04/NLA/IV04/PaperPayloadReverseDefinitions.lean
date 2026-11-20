module

public import NLA.IV04.PaperWordListProductDefinitions
public import NLA.IV04.PaperRationalListParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def payloadReverseStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let output := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (Complexity.pair (Complexity.pairFst rest) output)) state

def payloadReverseState (input : List Bool) : List Bool :=
  (payloadReverseStep^[input.length]) (Complexity.pair input [])

/-- Reverse nested payloads, preserving every bit within each payload. -/
def polynomialPayloadReverse (input : List Bool) : List Bool :=
  Complexity.pairSnd (payloadReverseState input)

end IV04.Paper.Computational
