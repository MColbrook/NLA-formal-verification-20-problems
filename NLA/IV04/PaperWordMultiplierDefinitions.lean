module

public import NLA.IV04.PaperWordAdderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Grade-school bit multiplication using the actual polynomial-time adder. -/
def polynomialWordMultiply : List Bool → List Bool → List Bool
  | [], _ => []
  | b :: left, right =>
      polynomialWordAdd (if b then right else []) (false :: polynomialWordMultiply left right)

def encodedPolynomialWordMultiply (input : List Bool) : List Bool :=
  polynomialWordMultiply (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
