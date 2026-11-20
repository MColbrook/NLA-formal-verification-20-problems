module

public import NLA.IV04.Complexitylib.SAT.CookLevin.Assembly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

/-- The pinned library proves Cook-Levin for its actual encoded CNF bit language. -/
theorem actual_binary_sat_np_complete : NPComplete SAT.language := SAT.NPComplete_language

theorem actual_np_language_reduces_to_binary_sat (L : Set (List Bool)) (hL : L ∈ NP) :
    L ≤ₚ SAT.language := SAT.NPHard_language L hL

#print axioms actual_binary_sat_np_complete
#print axioms actual_np_language_reduces_to_binary_sat
end IV04.Paper.Computational
