module

public import NLA.MI19.Definitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace NLA.MI19.LiteralProse
theorem literal_inversion_example :
    inversionCount (Equiv.swap (0 : Fin 4) 2) = 3 ∧
    inversionCount (Equiv.swap (0 : Fin 3) 1) = 1 ∧
    PreservesSubset (Equiv.swap (0 : Fin 4) 2) witnessSubset ∧
    ∀ i : Fin 3, (Equiv.swap (0 : Fin 4) 2) ((1 : Fin 4).succAbove i) =
      (1 : Fin 4).succAbove ((Equiv.swap (0 : Fin 3) 1) i) := by
  decide
end NLA.MI19.LiteralProse
