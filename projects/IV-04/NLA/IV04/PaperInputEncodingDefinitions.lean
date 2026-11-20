module

public import NLA.IV04.PaperEncodingDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper

/-- Decode a counted list of actual binary natural numbers. -/
def readNaturals : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bits => some ([],bits)
  | n+1, bits => do
      let (value,tail) ← readNatural bits
      let (values,last) ← readNaturals n tail
      return (value :: values,last)

/-- Raw counted-weight parser; positivity is an input validity condition. -/
def readIntegerWeights (bits : List Bool) : Option (List ℕ × List Bool) := do
  let (count,tail) ← readNatural bits
  readNaturals count tail

namespace IntegerPartition

def weightList (P : IntegerPartition) : List ℕ := List.ofFn P.weight
def inputCode (P : IntegerPartition) : List Bool :=
  naturalCode P.m ++ P.weightList.flatMap naturalCode

end IntegerPartition
end IV04.Paper
