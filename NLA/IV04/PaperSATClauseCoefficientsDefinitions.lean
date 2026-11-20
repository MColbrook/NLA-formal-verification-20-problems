module

public import NLA.IV04.PaperSATLiteralMatchDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- The output is last so that appending a coefficient does not duplicate the accumulated table. -/
def clauseCoefficientPack (rest query output : List Bool) : List Bool :=
  Complexity.pair rest (Complexity.pair query output)
def clauseCoefficientStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let query := Complexity.pairFst (Complexity.pairSnd state)
  let output := Complexity.pairSnd (Complexity.pairSnd state)
  let coefficient := polynomialLiteralMatchCount (Complexity.pair (Complexity.pairFst rest) query)
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (clauseCoefficientPack (Complexity.pairSnd rest) query (Complexity.pair coefficient output)) state
def clauseCoefficientState (input : List Bool) : List Bool :=
  (clauseCoefficientStep^[input.length])
    (clauseCoefficientPack (Complexity.pairFst input) (Complexity.pairSnd input) [])
def polynomialSATClauseCoefficients (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (clauseCoefficientState input))
end IV04.Paper.Computational
