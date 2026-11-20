module

public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperCountedMachineDefinitions
public import NLA.IV04.PaperMatrixCoefficientInputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def budgetedPowerStep (state : List Bool) : List Bool :=
  let count := Complexity.pairFst state
  let base := Complexity.pairFst (Complexity.pairSnd state)
  let product := Complexity.pairSnd (Complexity.pairSnd state)
  Complexity.caseBit₀ (Complexity.nonemptyFlag count)
    (Complexity.pair (decrementCount count) (Complexity.pair base (canonicalWordMultiply product base))) state

/-- The input is count, base and padding. Padding contributes only to the clock.
Even an exponentially large binary count causes at most physical-input-length steps. -/
def budgetedPowerState (input : List Bool) : List Bool :=
  (budgetedPowerStep^[input.length])
    (Complexity.pair (canonicalWord (Complexity.pairFst input))
      (Complexity.pair (Complexity.pairFst (Complexity.pairSnd input)) [true]))

def polynomialBudgetedPower (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (budgetedPowerState input))

def matrixDenominatorPowerArgument (input : List Bool) : List Bool :=
  let decoded := encodedMatrixCoefficientInput input
  Complexity.pair (Complexity.pairFst (Complexity.pairSnd decoded))
    (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd decoded))) input)

def encodedMatrixDenominatorPower (input : List Bool) : List Bool :=
  polynomialBudgetedPower (matrixDenominatorPowerArgument input)

end IV04.Paper.Computational
