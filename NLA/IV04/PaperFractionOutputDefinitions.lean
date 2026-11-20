module

public import NLA.IV04.PaperFractionWordDefinitions
public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
/-- Serialize the actual signed numerator and denominator, without requiring fraction reduction. -/
def polynomialFractionOutput (input : List Bool) : List Bool :=
  let fields := canonicalWordCode (pairFst input).tail ++ canonicalWordCode (pairSnd input)
  caseBit₀ (bitAt [] (pairFst input)) (true :: fields) (false :: fields)
end IV04.Paper.Computational
