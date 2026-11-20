module

public import NLA.IV04.PaperSATVariableMarkersDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- An actual guarded loop concatenates chunks emitted by a string program at each binary index.
The physical ruler limits every input, including malformed or oversized bounds. -/
def boundedPayloadMapStep (f : List Bool → List Bool) (state : List Bool) : List Bool :=
  let index := Complexity.pairFst state
  let bound := Complexity.pairFst (Complexity.pairSnd state)
  let query := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
  let output := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))
  Complexity.caseBit₀ (Complexity.notBit (polynomialWordLe bound index))
    (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound query
      (f (Complexity.pair query index) ++ output)) state
def boundedPayloadMapState (f : List Bool → List Bool) (input : List Bool) : List Bool :=
  ((boundedPayloadMapStep f)^[(Complexity.pairFst input).length+1])
    (variableMarkerPack [] (Complexity.pairFst (Complexity.pairSnd input))
      (Complexity.pairSnd (Complexity.pairSnd input)) [])
def polynomialBoundedPayloadMap (f : List Bool → List Bool) (input : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (boundedPayloadMapState f input)))
end IV04.Paper.Computational
