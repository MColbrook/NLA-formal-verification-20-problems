module

public import NLA.IV04.PaperCanonicalWordDefinitions
public import NLA.IV04.PaperWordMultiplierDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def canonicalWordMultiply (left right : List Bool) : List Bool :=
  canonicalWord (polynomialWordMultiply left right)

def encodedCanonicalWordMultiply (input : List Bool) : List Bool :=
  canonicalWordMultiply (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
