module

public import NLA.IV04.PaperDenseContinuantDeterminantDefinitions
public import NLA.IV04.PaperStrictMatrixValidationDefinitions
public import NLA.IV04.PaperMatrixDenseSupportDefinitions
public import NLA.IV04.PaperBudgetedPowerDefinitions
public import NLA.IV04.PaperScaledThresholdDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def matrixDeterminantThresholdFields (selected power : List Bool) : List Bool :=
  let dimension := Complexity.pairFst (Complexity.pairSnd selected)
  let denominator := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd selected))
  let body := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd selected)))
  let words := Complexity.pairFst body
  let threshold := Complexity.pairFst (Complexity.pairFst (Complexity.pairSnd body))
  Complexity.pair (polynomialDenseIntegerDeterminant (Complexity.pair dimension words))
    (Complexity.pair threshold (Complexity.pair denominator power))

def matrixDeterminantThresholdArgument (input : List Bool) : List Bool :=
  matrixDeterminantThresholdFields (encodedOrderedMatrixVertexSelection input)
    (encodedMatrixDenominatorPower (Complexity.pairFst input))

/-- Actual certificate verifier: strict decoding/consumption, both-endpoint support,
then the determinant threshold of the selected row-major matrix. -/
def encodedMatrixDeterminantVerifier (input : List Bool) : List Bool :=
  Complexity.andBit (encodedStrictMatrixSelectionFlag input)
    (Complexity.andBit (encodedMatrixDenseSupportFlag (Complexity.pairFst input))
      (encodedScaledDeterminantThreshold (matrixDeterminantThresholdArgument input)))

end IV04.Paper.Computational