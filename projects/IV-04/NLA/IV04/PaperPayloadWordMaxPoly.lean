module

public import NLA.IV04.PaperPayloadWordMaxBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

 theorem polynomial_word_max_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordMax (v 0) (v 1) :=
  (Cobham.iteFn polynomial_word_le_cobham (.proj 1) (.proj 0)).of_eq fun _ => rfl

 theorem payload_word_max_step_cobham (select : List Bool → List Bool)
    (hselect : Cobham fun v : Fin 1 → List Bool => select (v 0)) :
    Cobham fun v : Fin 1 → List Bool => payloadWordMaxStep select (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hm := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.comp hselect fun _ : Fin 1 => Cobham.fstBlockFn hr
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr)
    (Cobham.comp₂ polynomial_word_max_cobham hm hc)
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (.proj 0)).of_eq fun _ => rfl

 theorem payload_word_max_state_cobham (select : List Bool → List Bool) (d : ℕ)
    (hselect : Cobham fun v : Fin 1 → List Bool => select (v 0))
    (hbound : ∀ input, (select input).length ≤ 2*input.length+d) :
    Cobham fun v : Fin 1 → List Bool => payloadWordMaxState select (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => payloadWordMaxStep select (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 2 false ++ smash (v 0) (List.replicate d false)
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [])
  have hs : Cobham step :=
    (Cobham.comp (payload_word_max_step_cobham select hselect) fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 2 false)))
    (Cobham.comp₂ Cobham.smash (.proj 0) (.const (List.replicate d false)))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change (((payloadWordMaxStep select)^[clock.length]) (pair (v 0) [])).length ≤ _
    have h := payload_word_max_clock_length select d hbound clock (v 0)
    simp [ruler,Complexity.smash,List.length_replicate]
    have hmul : clock.length*d=d*clock.length := Nat.mul_comm _ _
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

 theorem polynomial_payload_word_max_cobham (select : List Bool → List Bool) (d : ℕ)
    (hselect : Cobham fun v : Fin 1 → List Bool => select (v 0))
    (hbound : ∀ input, (select input).length ≤ 2*input.length+d) :
    Cobham fun v : Fin 1 → List Bool => polynomialPayloadWordMax select (v 0) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.sndBlockFn (payload_word_max_state_cobham select d hselect hbound)).of_eq fun _ => rfl

end IV04.Paper.Computational
