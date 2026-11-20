module

public import NLA.IV04.PaperSATRawLiteralDefinitions
public import NLA.IV04.PaperPayloadReverseDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

/-- Physical unread input, forward raw literal, reversed clause payloads,
    reversed completed CNF payloads, and the persistent validity flag. -/
def satCNFPack (rest raw clause formula valid : List Bool) : List Bool :=
  pair rest (pair raw (pair clause (pair formula valid)))

def satCNFRest (state : List Bool) := pairFst state
def satCNFRaw (state : List Bool) := pairFst (pairSnd state)
def satCNFClause (state : List Bool) := pairFst (pairSnd (pairSnd state))
def satCNFFormula (state : List Bool) := pairFst (pairSnd (pairSnd (pairSnd state)))
def satCNFValid (state : List Bool) := pairSnd (pairSnd (pairSnd (pairSnd state)))

/-- Consume one actual two-bit SAT token. An odd final bit permanently rejects. -/
def satCNFParseStep (state : List Bool) : List Bool :=
  let rest := satCNFRest state
  let raw := satCNFRaw state
  let clause := satCNFClause state
  let formula := satCNFFormula state
  let valid := satCNFValid state
  let next := rest.tail.tail
  let data := satCNFPack next (raw ++ bitAt [] rest) clause formula valid
  let literal := polynomialSATRawLiteral raw
  let lit := satCNFPack next [] (pair (pairSnd literal) clause) formula
    (andBit valid (pairFst literal))
  let close := satCNFPack next [] [] (pair clause formula)
    (andBit valid (notBit (nonemptyFlag raw)))
  caseBit₀ (nonemptyFlag rest)
    (caseBit₀ (nonemptyFlag rest.tail)
      (caseBit₀ (bitAt [] rest) (caseBit₀ (bitAt [] rest.tail) data close)
        (caseBit₀ (bitAt [] rest.tail) lit data))
      (satCNFPack [] raw clause formula [false])) state

def satCNFParseState (input : List Bool) : List Bool :=
  (satCNFParseStep^[input.length]) (satCNFPack input [] [] [] [true])

def satCNFFinalFlag (state : List Bool) : List Bool :=
  andBit (satCNFValid state)
    (andBit (notBit (nonemptyFlag (satCNFRest state)))
      (andBit (notBit (nonemptyFlag (satCNFRaw state)))
        (notBit (nonemptyFlag (satCNFClause state)))))

/-- Complete actual CNF parser. Formula order is restored; each clause keeps
    reverse literal order, which its explicit payload specification records. -/
def polynomialSATCNFParse (input : List Bool) : List Bool :=
  let state := satCNFParseState input
  pair (satCNFFinalFlag state) (polynomialPayloadReverse (satCNFFormula state))

end IV04.Paper.Computational
