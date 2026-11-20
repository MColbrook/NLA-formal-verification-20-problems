module

public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperWordListSumDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Consume one nested binary coefficient and perform the actual Horner update. -/
def wordListHornerStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let base := Complexity.pairFst (Complexity.pairSnd state)
  let total := Complexity.pairSnd (Complexity.pairSnd state)
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest) (Complexity.pair base
      (polynomialWordAdd (canonicalWordMultiply total base) (Complexity.pairFst rest)))) state

/-- Input consists of a binary base and a nested list of binary coefficients.
    Physical input length clocks every input, including malformed payloads. -/
def wordListHornerState (input : List Bool) : List Bool :=
  (wordListHornerStep^[input.length])
    (Complexity.pair (Complexity.pairSnd input) (Complexity.pair (Complexity.pairFst input) []))

def polynomialWordListHorner (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (wordListHornerState input))

end IV04.Paper.Computational
