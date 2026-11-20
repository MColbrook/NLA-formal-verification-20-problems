module

public import NLA.IV04.PaperCanonicalWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Count actual input bits using the certified binary adder. -/
def rawLengthWord : List Bool → List Bool
  | [] => []
  | _ :: bits => polynomialWordAdd [true] (rawLengthWord bits)

def inputLengthWord (input : List Bool) : List Bool := canonicalWord (rawLengthWord input)

end IV04.Paper.Computational
