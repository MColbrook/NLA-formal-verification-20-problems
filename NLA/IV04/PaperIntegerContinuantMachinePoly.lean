module

public import NLA.IV04.PaperIntegerContinuantMachineBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem integer_continuant_state_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => integerContinuantInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => integerContinuantStep (v 0)
  let clockTwo : (Fin 2 → List Bool) → List Bool := fun v => v 0 ++ v 0
  let clockFour : (Fin 2 → List Bool) → List Bool := fun v => clockTwo v ++ clockTwo v
  let clockEight : (Fin 2 → List Bool) → List Bool := fun v => clockFour v ++ clockFour v
  let inputTwo : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    clockEight v ++ clockFour v ++ inputTwo v ++ v 1 ++ List.replicate 10 false
  have hi : Cobham initial := integer_continuant_initial_cobham
  have hs : Cobham step :=
    (Cobham.comp integer_continuant_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hct : Cobham clockTwo := Cobham.appendFn (.proj 0) (.proj 0)
  have hcf : Cobham clockFour := Cobham.appendFn hct hct
  have hce : Cobham clockEight := Cobham.appendFn hcf hcf
  have hitwo : Cobham inputTwo := Cobham.appendFn (.proj 1) (.proj 1)
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn hce hcf) hitwo) (.proj 1))
    (.const (List.replicate 10 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((integerContinuantStep^[clock.length]) (integerContinuantInitial (v 0))).length ≤ _
    have h := integer_continuant_initial_iterate_length clock.length (v 0)
    simp [ruler,clockEight,clockFour,clockTwo,inputTwo]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem polynomial_integer_continuant_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialIntegerContinuant (v 0) :=
  (Cobham.fstBlockFn (Cobham.sndBlockFn integer_continuant_state_cobham)).of_eq fun _ => rfl

theorem polynomial_integer_continuant_mem_fp : polynomialIntegerContinuant ∈ FP :=
  CobhamFP_subset_FP polynomial_integer_continuant_cobham

#print axioms polynomial_integer_continuant_mem_fp
end IV04.Paper.Computational
