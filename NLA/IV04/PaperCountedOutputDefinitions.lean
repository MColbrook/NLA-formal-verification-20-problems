module

public import NLA.IV04.PaperCountedMachineDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def payloadListCode : List (List Bool) → List Bool
  | [] => []
  | payload :: rest => Complexity.pair payload (payloadListCode rest)

/-- Semantic decoder only; its fuel is the actual encoded output length. -/
def decodePayloads : ℕ → List Bool → List ℕ
  | 0, _ => []
  | fuel+1, input => if input=[] then [] else
      wordValue (Complexity.pairFst input) :: decodePayloads fuel (Complexity.pairSnd input)

def countedStateResult (state : List Bool) : Option (List ℕ × List Bool) :=
  if wordValue (countedCount state)=0 ∧ countedFlag state=[true] then
    some ((decodePayloads (countedOutput state).length (countedOutput state)).reverse,countedRest state)
  else none

def countedParserResult (input : List Bool) : Option (List ℕ × List Bool) :=
  let encoded := encodedCountedNaturalParser input
  if Complexity.pairFst encoded=[true] then
    let output := Complexity.pairFst (Complexity.pairSnd encoded)
    some ((decodePayloads output.length output).reverse,Complexity.pairSnd (Complexity.pairSnd encoded))
  else none

/-- Structured reference for the exact same step program and its reversed payload output. -/
def countedRun : ℕ → List Bool → Bool → List Bool → List (List Bool) → List Bool
  | 0, count, valid, rest, payloads => countedPack count [valid] rest (payloadListCode payloads)
  | fuel+1, count, valid, rest, payloads =>
      if wordValue count=0 then countedRun fuel count valid rest payloads
      else if valid then
        if Complexity.pairFst (encodedNaturalParser rest)=[true] then
          countedRun fuel (decrementCount count) true
            (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser rest)))
            (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser rest)) :: payloads)
        else countedRun fuel count false rest payloads
      else countedRun fuel count valid rest payloads

end IV04.Paper.Computational
