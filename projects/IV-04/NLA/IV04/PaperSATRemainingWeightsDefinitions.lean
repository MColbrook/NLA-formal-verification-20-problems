module

public import NLA.IV04.PaperSATLiteralDigitsDefinitions
public import NLA.IV04.PaperBoundedPayloadRepeatDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
def polynomialSATClauseTarget (formula : List Bool) : List Bool :=
  let metadata := polynomialSATMetadata formula
  canonicalWordMultiply (Complexity.pairFst metadata)
    (Complexity.pairSnd (Complexity.pairSnd metadata))
/-- A slack query is an original SAT input paired with a binary clause index. -/
def polynomialSATSlackDigits (input : List Bool) : List Bool :=
  let bits := Complexity.pairFst input
  let query := Complexity.pairSnd input
  let formula := Complexity.pairSnd (polynomialSATCNFParse bits)
  let metadata := polynomialSATMetadata formula
  polynomialSATVariableMarkers (Complexity.pair bits
    (Complexity.pair (Complexity.pairFst (Complexity.pairSnd metadata)) query)) ++
    polynomialBoundedPayloadRepeat (Complexity.pair bits (Complexity.pair (Complexity.pairFst metadata) []))
def polynomialSATSlackWeight (input : List Bool) : List Bool :=
  let formula := Complexity.pairSnd (polynomialSATCNFParse (Complexity.pairFst input))
  canonicalWord (polynomialWordListHorner
    (Complexity.pair (polynomialSATDigitBase formula) (polynomialSATSlackDigits input)))
def polynomialSATTargetDigits (bits : List Bool) : List Bool :=
  let formula := Complexity.pairSnd (polynomialSATCNFParse bits)
  let metadata := polynomialSATMetadata formula
  polynomialBoundedPayloadRepeat (Complexity.pair bits
    (Complexity.pair (Complexity.pairFst (Complexity.pairSnd metadata)) (polynomialSATClauseTarget formula))) ++
    polynomialBoundedPayloadRepeat (Complexity.pair bits (Complexity.pair (Complexity.pairFst metadata) [true]))
def polynomialSATTargetWeight (bits : List Bool) : List Bool :=
  let formula := Complexity.pairSnd (polynomialSATCNFParse bits)
  canonicalWord (polynomialWordListHorner
    (Complexity.pair (polynomialSATDigitBase formula) (polynomialSATTargetDigits bits)))
end IV04.Paper.Computational
