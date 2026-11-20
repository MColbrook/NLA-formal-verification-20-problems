module

public import NLA.IV04.PaperSATCNFParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

/-- Exact binary variable/polarity fields emitted by the literal parser. -/
def satLiteralPayload (lit : SAT.Lit) : List Bool := pair lit.var.bits [lit.sign]

def satClausePayload (clause : SAT.Clause) : List Bool :=
  payloadListCode (clause.map satLiteralPayload)

/-- CNF order is forward; individual clauses explicitly have reverse literal order. -/
def satFormulaPayload (formula : SAT.CNF) : List Bool :=
  payloadListCode (formula.map fun clause => satClausePayload clause.reverse)

/-- The original pinned decoder continued from an actual typed parser state. -/
def satCNFActualFrom (bits rawRev : List Bool) (clauseRev : SAT.Clause) (formulaRev : SAT.CNF) :
    Option SAT.CNF :=
  (SAT.tokenize? bits).bind fun tokens => SAT.parseTokensAux tokens rawRev clauseRev formulaRev

/-- Literal program output agrees with success or rejection of the actual decoder. -/
def satCNFOutcome (result : Option SAT.CNF) (state : List Bool) : Prop :=
  match result with
  | none => satCNFFinalFlag state=[false]
  | some formula => satCNFFinalFlag state=[true] ∧
      polynomialPayloadReverse (satCNFFormula state)=satFormulaPayload formula

end IV04.Paper.Computational
