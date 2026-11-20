module

public import NLA.IV04.PaperInputEncodingDefinitions
public import NLA.IV04.PaperNaturalParserDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- A semantic reference with a clock bounded by input bit length, even for bad counts. -/
def fuelReadNaturals : ℕ → ℕ → List Bool → Option (List ℕ × List Bool)
  | _, 0, input => some ([],input)
  | 0, _+1, _ => none
  | fuel+1, count+1, input => do
      let (value,rest) ← IV04.Paper.readNatural input
      let (values,tail) ← fuelReadNaturals fuel count rest
      return (value :: values,tail)

def boundedReadIntegerWeights (input : List Bool) : Option (List ℕ × List Bool) := do
  let (count,rest) ← IV04.Paper.readNatural input
  fuelReadNaturals input.length count rest

end IV04.Paper.Computational
