module

public import NLA.IV04.PaperWordAdderDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Consume one nested payload and add its binary natural value to the accumulator. -/
def wordListSumStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let total := Complexity.pairSnd state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (Complexity.pair (Complexity.pairSnd rest)
      (polynomialWordAdd total (Complexity.pairFst rest))) state

def wordListSumState (input : List Bool) : List Bool :=
  (wordListSumStep^[input.length]) (Complexity.pair input [])

def polynomialWordListSum (input : List Bool) : List Bool :=
  Complexity.pairSnd (wordListSumState input)

/-- Total binary program; semantic correctness is asserted when the counted parser succeeds. -/
def polynomialParsedWeightTotal (input : List Bool) : List Bool :=
  polynomialWordListSum (Complexity.pairFst (Complexity.pairSnd (encodedCountedNaturalParser input)))

end IV04.Paper.Computational
