module

public import NLA.IV04.PaperSATLiteralMatchDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
def variableMarkerPack (index bound query output : List Bool) : List Bool :=
  Complexity.pair index (Complexity.pair bound (Complexity.pair query output))
def variableMarkerDigit (index query : List Bool) : List Bool :=
  Complexity.caseBit₀ (literalMatchFlag (Complexity.pair index [false]) (Complexity.pair query [false])) [true] []
def variableMarkerStep (state : List Bool) : List Bool :=
  let index := Complexity.pairFst state
  let bound := Complexity.pairFst (Complexity.pairSnd state)
  let query := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
  let output := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))
  Complexity.caseBit₀ (Complexity.notBit (polynomialWordLe bound index))
    (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound query
      (Complexity.pair (variableMarkerDigit index query) output)) state
/-- The first field is a physical ruler. Binary bound values never determine the clock. -/
def variableMarkerState (input : List Bool) : List Bool :=
  (variableMarkerStep^[(Complexity.pairFst input).length+1])
    (variableMarkerPack [] (Complexity.pairFst (Complexity.pairSnd input))
      (Complexity.pairSnd (Complexity.pairSnd input)) [])
def polynomialSATVariableMarkers (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (variableMarkerState input)))
end IV04.Paper.Computational
