module

public import NLA.IV04.PaperWordListHornerBounds
public import NLA.IV04.PaperWordListSumPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem word_list_horner_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListHornerStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hm := Cobham.comp₂ canonical_word_multiply_cobham ht hb
  have ha := Cobham.comp₂ polynomial_word_add_cobham hm (Cobham.fstBlockFn hr)
  have hn := (Cobham.comp₂ Cobham.pairing) (Cobham.sndBlockFn hr) ((Cobham.comp₂ Cobham.pairing) hb ha)
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (.proj 0)).of_eq fun _ => rfl

theorem word_list_horner_state_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListHornerState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v =>
    pair (pairSnd (v 0)) (pair (pairFst (v 0)) [])
  let step : (Fin 2 → List Bool) → List Bool := fun v => wordListHornerStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ v 1 ++ v 1 ++ List.replicate 4 false ++ smash (v 0) (false::v 1)
  have hi : Cobham initial := (Cobham.comp₂ Cobham.pairing) (Cobham.sndBlockFn (.proj 0))
    ((Cobham.comp₂ Cobham.pairing) (Cobham.fstBlockFn (.proj 0)) (.const []))
  have hs : Cobham step :=
    (Cobham.comp word_list_horner_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
      (.proj 1)) (.proj 1)) (.const (List.replicate 4 false)))
    ((Cobham.comp₂ Cobham.smash (.proj 0) (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => .proj 1)).of_eq fun _ => rfl)
  have hbound : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((wordListHornerStep^[clock.length])
      (pair (pairSnd (v 0)) (pair (pairFst (v 0)) []))).length ≤ _
    have h := word_list_horner_clock_length clock (v 0)
    simp [ruler,smash_length]
    nlinarith only [h]
  have hit := Cobham.iterFn hi hs hr hbound
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_word_list_horner_mem_fp : polynomialWordListHorner ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn (Cobham.sndBlockFn word_list_horner_state_cobham)).of_eq fun _ => rfl)

#print axioms polynomial_word_list_horner_mem_fp
end IV04.Paper.Computational
