module

public import NLA.IV04.PaperWordListProductDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def polynomialPositiveWordList (input : List Bool) : List Bool :=
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord (polynomialWordListProduct input)))
    [true] [false]

def polynomialNonemptyPositiveWordList (input : List Bool) : List Bool :=
  Complexity.andBit (Complexity.nonemptyFlag input) (polynomialPositiveWordList input)

end IV04.Paper.Computational
