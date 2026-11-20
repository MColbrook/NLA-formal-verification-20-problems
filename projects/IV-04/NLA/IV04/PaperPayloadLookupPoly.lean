module

public import NLA.IV04.PaperPayloadLookupBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem payload_lookup_step_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadLookupStep (v 0) := by
  have hc := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hf := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  have hd := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hc
  exact (Cobham.iteFn hn (Cobham.comp₂ Cobham.pairing hd (Cobham.sndBlockFn hf))
    (Cobham.comp₂ Cobham.pairing hc hf)).of_eq fun _ => rfl

theorem payload_lookup_state_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadLookupState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (pairFst (v 0)) (pairSnd (v 0))
  let step : (Fin 2 → List Bool) → List Bool := fun v => payloadLookupStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1 ++ [false,false]
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (.proj 0)) (Cobham.sndBlockFn (.proj 0))
  have hs : Cobham step := (Cobham.comp payload_lookup_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const [false,false])
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun state => step (Fin.cons state v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    simpa [ruler,initial,step,two_mul,Nat.add_assoc] using payload_lookup_iterate_length clock.length (v 0)
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by intro i;fin_cases i <;> simpa [args] using Cobham.proj (0 : Fin 1)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem polynomial_payload_lookup_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPayloadLookup (v 0) :=
  (Cobham.fstBlockFn (Cobham.sndBlockFn payload_lookup_state_cobham)).of_eq fun _ => rfl

theorem polynomial_payload_lookup_mem_fp : polynomialPayloadLookup ∈ FP :=
  CobhamFP_subset_FP polynomial_payload_lookup_cobham

#print axioms polynomial_payload_lookup_mem_fp
end IV04.Paper.Computational
