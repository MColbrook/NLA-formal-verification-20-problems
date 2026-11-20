module

public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem word_list_product_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListProductStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hp := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr)
    (Cobham.comp₂ canonical_word_multiply_cobham hp (Cobham.fstBlockFn hr))
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (Cobham.proj 0)).of_eq fun _ => rfl

theorem word_list_product_state_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListProductState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) [true]
  let step : (Fin 2 → List Bool) → List Bool := fun v => wordListProductStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1 ++ List.replicate 3 false
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [true])
  have hs : Cobham step :=
    (Cobham.comp word_list_product_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 3 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((wordListProductStep^[clock.length]) (pair (v 0) [true])).length ≤ _
    have h := word_list_product_iterate_length clock.length (v 0) [true]
    simp only [List.length_cons,List.length_nil] at h
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_word_list_product_mem_fp : polynomialWordListProduct ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn word_list_product_state_cobham).of_eq fun _ => rfl)

#print axioms polynomial_word_list_product_mem_fp
end IV04.Paper.Computational
