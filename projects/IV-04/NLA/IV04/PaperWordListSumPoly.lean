module

public import NLA.IV04.PaperWordListSumBounds
public import NLA.IV04.PaperCountedMachinePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem word_list_sum_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListSumStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have ht := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr)
    (Cobham.comp₂ polynomial_word_add_cobham ht (Cobham.fstBlockFn hr))
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (Cobham.proj 0)).of_eq fun _ => rfl

theorem word_list_sum_state_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListSumState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => wordListSumStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 0 ++ v 1 ++ v 1 ++ List.replicate 2 false
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [])
  have hs : Cobham step :=
    (Cobham.comp word_list_sum_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 1)) (.proj 1)) (.const (List.replicate 2 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((wordListSumStep^[clock.length]) (pair (v 0) [])).length ≤ _
    have h := word_list_sum_iterate_length clock.length (v 0) []
    simp only [List.length_nil] at h
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_word_list_sum_mem_fp : polynomialWordListSum ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn word_list_sum_state_cobham).of_eq fun _ => rfl)

theorem parsed_weight_total_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialParsedWeightTotal (v 0) := by
  have ho := Cobham.fstBlockFn (Cobham.sndBlockFn encoded_counted_natural_parser_cobham)
  have hs := (Cobham.sndBlockFn word_list_sum_state_cobham).of_eq fun _ => rfl
  exact (Cobham.comp hs fun _ : Fin 1 => ho).of_eq fun _ => rfl

theorem parsed_weight_total_mem_fp : polynomialParsedWeightTotal ∈ FP :=
  CobhamFP_subset_FP parsed_weight_total_cobham

#print axioms parsed_weight_total_mem_fp
end IV04.Paper.Computational
