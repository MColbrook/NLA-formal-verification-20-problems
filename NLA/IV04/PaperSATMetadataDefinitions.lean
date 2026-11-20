module

public import NLA.IV04.PaperPayloadWordMaxDefinitions
public import NLA.IV04.PaperNestedPayloadCountDefinitions
public import NLA.IV04.PaperSATCNFParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Largest actual binary literal variable in a clause table. -/
def polynomialSATClauseMaximum : List Bool → List Bool := polynomialPayloadWordMax Complexity.pairFst

/-- Largest actual variable in the nested clause table. -/
def polynomialSATFormulaMaximum : List Bool → List Bool :=
  polynomialPayloadWordMax polynomialSATClauseMaximum

/-- Actual binary (variable count, clause count, literal budget) fields. -/
def polynomialSATMetadata (input : List Bool) : List Bool :=
  Complexity.pair (canonicalWord (polynomialWordAdd (polynomialSATFormulaMaximum input) [true]))
    (Complexity.pair (polynomialPayloadCount input)
      (canonicalWord (polynomialWordAdd (polynomialNestedPayloadCount input) [true])))

/-- Retain the original decoder flag with exact metadata from the emitted table. -/
def polynomialSATInputMetadata (input : List Bool) : List Bool :=
  let parsed := polynomialSATCNFParse input
  Complexity.pair (Complexity.pairFst parsed) (polynomialSATMetadata (Complexity.pairSnd parsed))

end IV04.Paper.Computational
