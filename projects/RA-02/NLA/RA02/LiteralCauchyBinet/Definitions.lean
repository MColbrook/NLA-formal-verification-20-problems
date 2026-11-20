module

public import NLA.RA02.PaperSharpDefinitions
public import Mathlib.Data.Finset.Sort

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA02CauchyBinet

abbrev SizedSubset (n s : ℕ) := {T : Finset (Fin n) // T.card = s}

def enumerate {n s : ℕ} (T : SizedSubset n s) : Fin s ↪ Fin n :=
  (T.val.orderEmbOfFin T.property).toEmbedding

def subsetExponent {n s : ℕ} (T : SizedSubset n s) : ℕ := ∑ j ∈ T.val, j.val

end RootRA02CauchyBinet
