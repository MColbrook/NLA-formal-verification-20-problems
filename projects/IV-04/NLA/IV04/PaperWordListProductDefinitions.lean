module

public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions
public import Mathlib.Logic.Function.Iterate

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- One input-field multiplication; malformed tails terminate at the empty string. -/
def wordListProductStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let product := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (canonicalWordMultiply product (Complexity.pairFst rest))) state

def wordListProductState (input : List Bool) : List Bool :=
  (wordListProductStep^[input.length]) (Complexity.pair input [true])

def polynomialWordListProduct (input : List Bool) : List Bool :=
  Complexity.pairSnd (wordListProductState input)

end IV04.Paper.Computational
