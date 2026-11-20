module

public import NLA.IV04.PaperRationalListParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def rationalListStateResult (state : List Bool) : Option (List ℚ × List Bool) :=
  if wordValue (countedCount state)=0 ∧ countedFlag state=[true] then
    some ((decodeFractionPayloads (countedOutput state).length (countedOutput state)).reverse,countedRest state)
  else none

/-- Structured reference for the same concrete step program. -/
def rationalListRun : ℕ → List Bool → Bool → List Bool → List (List Bool) → List Bool
  | 0, count, valid, rest, payloads => countedPack count [valid] rest (payloadListCode payloads)
  | fuel+1, count, valid, rest, payloads =>
      if wordValue count=0 then rationalListRun fuel count valid rest payloads
      else if valid then
        if Complexity.pairFst (encodedRationalParser rest)=[true] then
          rationalListRun fuel (decrementCount count) true
            (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser rest)))
            (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser rest)) :: payloads)
        else rationalListRun fuel count false rest payloads
      else rationalListRun fuel count valid rest payloads

end IV04.Paper.Computational
