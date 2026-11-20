module

public import NLA.IV04.Complexitylib.SAT.CookLevin.Assembly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.ComplexityFoundation

theorem verified_sat_mem_np :
    Complexity.SAT.language ∈ Complexity.NP := by
  exact Complexity.SAT.language_mem_NP

theorem verified_sat_np_hard :
    ∀ L ∈ Complexity.NP,
      ∃ f : List Bool → List Bool, f ∈ Complexity.FP ∧
        ∀ x, x ∈ L ↔ f x ∈ Complexity.SAT.language := by
  exact Complexity.SAT.NPHard_language

theorem verified_sat_np_complete :
    Complexity.SAT.language ∈ Complexity.NP ∧
      ∀ L ∈ Complexity.NP,
        ∃ f : List Bool → List Bool, f ∈ Complexity.FP ∧
          ∀ x, x ∈ L ↔ f x ∈ Complexity.SAT.language := by
  exact Complexity.SAT.NPComplete_language

theorem verified_cobham_eq_machine_fp :
    Complexity.CobhamFP = Complexity.FP := by
  exact Complexity.CobhamFP_eq_FP

#print axioms IV04.ComplexityFoundation.verified_sat_mem_np
#print axioms IV04.ComplexityFoundation.verified_sat_np_hard
#print axioms IV04.ComplexityFoundation.verified_sat_np_complete
#print axioms IV04.ComplexityFoundation.verified_cobham_eq_machine_fp
end IV04.ComplexityFoundation
