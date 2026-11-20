module

public import NLA.IV04.PaperCountedMachineBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem counted_machine_state_cobham :
    Cobham fun v : Fin 1 → List Bool => countedMachineState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => countedInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => countedStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ v 1 ++ v 1 ++ List.replicate 8 false
  have hi : Cobham initial := counted_initial_cobham
  have hs : Cobham step :=
    (Cobham.comp counted_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
      (.proj 1) (.proj 1)) (.proj 1)) (.proj 1)) (.const (List.replicate 8 false))
  have hbound : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((countedStep^[clock.length]) (countedInitial (v 0))).length ≤ _
    have h := counted_initial_iterate_length clock.length (v 0)
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hbound
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem encoded_counted_natural_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedCountedNaturalParser (v 0) := by
  have h := counted_machine_state_cobham
  have hc := Cobham.fstBlockFn h
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn h)
  have hr := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h))
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h))
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.comp₂ Cobham.pairing (Cobham.iteFn hn (Cobham.const [false]) hf)
    (Cobham.comp₂ Cobham.pairing ho hr)).of_eq fun _ => rfl

theorem encoded_counted_natural_parser_mem_fp : encodedCountedNaturalParser ∈ FP :=
  CobhamFP_subset_FP encoded_counted_natural_parser_cobham

#print axioms encoded_counted_natural_parser_mem_fp
end IV04.Paper.Computational
