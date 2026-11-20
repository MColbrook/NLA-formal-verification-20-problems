module

public import NLA.MI19.Definitions

@[expose] public section

set_option autoImplicit false
namespace NLA.MI19.MovingTerms

/-- An integer copy used only to perform the finite sign computation.
Its cast is proved equal to the manuscript's complex Gram matrix. -/
def integerWitness : Matrix (Fin 4) (Fin 4) ℤ :=
  !![170, 1, 167, 170; 1, 1, -2, 1; 167, -2, 173, 167; 170, 1, 167, 170]

end NLA.MI19.MovingTerms
