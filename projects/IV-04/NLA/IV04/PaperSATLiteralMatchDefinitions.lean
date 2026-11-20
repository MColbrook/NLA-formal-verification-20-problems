module

public import NLA.IV04.PaperWordComparisonDefinitions
public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Actual binary equality of the variable field and equality of the polarity bit. -/
def literalMatchFlag (literal query : List Bool) : List Bool :=
  Complexity.andBit
    (Complexity.andBit (polynomialWordLe (Complexity.pairFst literal) (Complexity.pairFst query))
      (polynomialWordLe (Complexity.pairFst query) (Complexity.pairFst literal)))
    (Complexity.notBit (xorFlag (Complexity.bitAt [] (Complexity.pairSnd literal))
      (Complexity.bitAt [] (Complexity.pairSnd query))))

def literalMatchPack (rest count query : List Bool) : List Bool :=
  Complexity.pair rest (Complexity.pair count query)

def literalMatchStep (state : List Bool) : List Bool :=
  let rest := Complexity.pairFst state
  let count := Complexity.pairFst (Complexity.pairSnd state)
  let query := Complexity.pairSnd (Complexity.pairSnd state)
  let next := Complexity.caseBit₀ (literalMatchFlag (Complexity.pairFst rest) query)
    (polynomialWordAdd count [true]) count
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (literalMatchPack (Complexity.pairSnd rest) next query) state

def literalMatchState (input : List Bool) : List Bool :=
  (literalMatchStep^[input.length])
    (literalMatchPack (Complexity.pairFst input) [] (Complexity.pairSnd input))

def polynomialLiteralMatchCount (input : List Bool) : List Bool :=
  canonicalWord (Complexity.pairFst (Complexity.pairSnd (literalMatchState input)))

end IV04.Paper.Computational
