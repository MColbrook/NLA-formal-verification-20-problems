module

public import NLA.IV04.PaperMatrixDeterminantVerifierDefinitions
public import NLA.IV04.Complexitylib.Classes.P.Cobham.Internal.StringOps

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Canonical pairing and a linear certificate budget are checked by actual bit programs. -/
def encodedMatrixBoundedWitnessFlag (input : List Bool) : List Bool :=
  Complexity.andBit
    (Complexity.Cobham.eqFlag (Complexity.pair (Complexity.pairFst input) (Complexity.pairSnd input)) input)
    (Complexity.andBit
      (Complexity.Cobham.lenLeFlag (false :: Complexity.pairFst input) (Complexity.pairSnd input))
      (Complexity.Cobham.eqFlag (encodedMatrixDeterminantVerifier input) [true]))

def matrixBoundedWitness (matrix choices : List Bool) : Prop :=
  choices.length ≤ matrix.length+1 ∧ encodedMatrixDeterminantVerifier (Complexity.pair matrix choices)=[true]

/-- Actual binary certificate language; the bridge to all dense matrix inputs is separate. -/
def matrixVerifierLanguage : Set (List Bool) :=
  {matrix | ∃ choices, matrixBoundedWitness matrix choices}

end IV04.Paper.Computational