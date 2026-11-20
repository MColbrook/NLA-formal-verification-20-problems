module

public import NLA.IV04.PaperSATVariableMarkersDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- Repeat a fixed payload under a physical-input clock and an actual binary bound. -/
def boundedPayloadRepeatStep (state : List Bool) : List Bool :=
  let index := Complexity.pairFst state
  let bound := Complexity.pairFst (Complexity.pairSnd state)
  let coefficient := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
  let output := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))
  Complexity.caseBit₀ (Complexity.notBit (polynomialWordLe bound index))
    (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound coefficient
      (Complexity.pair coefficient output)) state
def boundedPayloadRepeatState (input : List Bool) : List Bool :=
  (boundedPayloadRepeatStep^[(Complexity.pairFst input).length+1])
    (variableMarkerPack [] (Complexity.pairFst (Complexity.pairSnd input))
      (Complexity.pairSnd (Complexity.pairSnd input)) [])
def polynomialBoundedPayloadRepeat (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (boundedPayloadRepeatState input)))
end IV04.Paper.Computational
