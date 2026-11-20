module

public import NLA.IV04.PaperLayerDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

def signAt (P : IntegerPartition) (sign : Fin P.m → ℤ) (i : ℕ) : ℤ :=
  if h : i < P.m then sign ⟨i,h⟩ else 1
def endpointParameters (P : IntegerPartition) (sign : Fin P.m → ℤ) (i : ℕ) : ℝ :=
  -(P.signAt sign i : ℝ)*(P.signAt sign (i+1) : ℝ)

end IV04.Paper.IntegerPartition
