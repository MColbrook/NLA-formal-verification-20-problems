module

public import NLA.IV04.PaperSATVariableMarkersDefinitions
public import NLA.IV04.PaperSATClauseCoefficientsDefinitions
public import NLA.IV04.PaperSATMetadataDefinitions
public import NLA.IV04.PaperWordListHornerInputDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
/-- Build all literal-weight digits directly from the original SAT bits and binary literal query. -/
def polynomialSATLiteralDigits (input : List Bool) : List Bool :=
  let bits := Complexity.pairFst input
  let query := Complexity.pairSnd input
  let formula := Complexity.pairSnd (polynomialSATCNFParse bits)
  let metadata := polynomialSATMetadata formula
  polynomialSATClauseCoefficients (Complexity.pair formula query) ++
    polynomialSATVariableMarkers (Complexity.pair bits
      (Complexity.pair (Complexity.pairFst metadata) (Complexity.pairFst query)))
def polynomialSATDigitBase (formula : List Bool) : List Bool :=
  let metadata := polynomialSATMetadata formula
  let target := canonicalWordMultiply (Complexity.pairFst metadata)
    (Complexity.pairSnd (Complexity.pairSnd metadata))
  canonicalWord (polynomialWordAdd (canonicalWordMultiply target [false,false,true]) [true,true])
def polynomialSATLiteralWeight (input : List Bool) : List Bool :=
  let formula := Complexity.pairSnd (polynomialSATCNFParse (Complexity.pairFst input))
  canonicalWord (polynomialWordListHorner
    (Complexity.pair (polynomialSATDigitBase formula) (polynomialSATLiteralDigits input)))
end IV04.Paper.Computational
