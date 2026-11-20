module

public import NLA.IV04.PaperRationalListMachineBounds
public import NLA.IV04.PaperRationalListMachineStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem rational_list_state_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => rationalListInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => rationalListStep (v 0)
  let scale : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ v 1 ++ v 1 ++ List.replicate 12 false
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    smash (v 0) (scale v) ++ v 1 ++ v 1 ++ List.replicate 8 false
  have hi : Cobham initial := rational_list_initial_cobham
  have hs : Cobham step :=
    (Cobham.comp rational_list_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hscale : Cobham scale :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
      (.proj 1) (.proj 1)) (.proj 1)) (.proj 1)) (.const (List.replicate 12 false))
  have hproduct := Cobham.comp₂ Cobham.smash (Cobham.proj (0 : Fin 2)) hscale
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn hproduct (.proj 1)) (.proj 1)) (.const (List.replicate 8 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((rationalListStep^[clock.length]) (rationalListInitial (v 0))).length ≤ _
    have h := rational_list_initial_iterate_length clock.length (v 0)
    simp [ruler,scale]
    nlinarith [h]
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem encoded_rational_list_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalListParser (v 0) := by
  have h := rational_list_state_cobham
  have hc := Cobham.fstBlockFn h
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn h)
  have hr := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h))
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h))
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.comp₂ Cobham.pairing (Cobham.iteFn hn (Cobham.const [false]) hf)
    (Cobham.comp₂ Cobham.pairing ho hr)).of_eq fun _ => rfl

theorem encoded_rational_list_parser_mem_fp : encodedRationalListParser ∈ FP :=
  CobhamFP_subset_FP encoded_rational_list_parser_cobham

#print axioms encoded_rational_list_parser_mem_fp
end IV04.Paper.Computational
