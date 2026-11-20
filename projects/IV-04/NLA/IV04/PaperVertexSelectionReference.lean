module

public import NLA.IV04.PaperVertexSelectionDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def endpointWordPairsCode : List (List Bool × List Bool) → List Bool → List Bool
  | [], rest => rest
  | (lower,upper)::rows, rest =>
      Complexity.pair lower (Complexity.pair upper (endpointWordPairsCode rows rest))

def selectedEndpointWords : List (List Bool × List Bool) → List Bool → List (List Bool)
  | [], _ => []
  | (lower,upper)::rows, choices =>
      (if choices.headD false then upper else lower)::selectedEndpointWords rows choices.tail

def endpointWordsOrdered (rows : List (List Bool × List Bool)) : Prop :=
  ∀ row ∈ rows, signedWordValue row.1 ≤ signedWordValue row.2

def vertexSelectionInputCode (rows : List (List Bool × List Bool))
    (rest choices : List Bool) : List Bool :=
  Complexity.pair rows.length.bits (Complexity.pair (endpointWordPairsCode rows rest) choices)

end IV04.Paper.Computational
