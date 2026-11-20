module

public import NLA.IV04.PaperPayloadCountBounds
public import NLA.IV04.PaperCanonicalWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

 theorem payload_count_step_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadCountStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr)
    (Cobham.comp₂ polynomial_word_add_cobham hc (Cobham.const [true]))
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (.proj 0)).of_eq fun _ => rfl

 theorem payload_count_state_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadCountState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => payloadCountStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 2 false ++ v 0 ++ v 0
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [])
  have hs : Cobham step :=
    (Cobham.comp payload_count_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
      (.const (List.replicate 2 false))) (.proj 0)) (.proj 0)
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((payloadCountStep^[clock.length]) (pair (v 0) [])).length ≤ _
    have h := payload_count_clock_length clock (v 0)
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

 theorem polynomial_payload_count_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPayloadCount (v 0) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.sndBlockFn payload_count_state_cobham).of_eq fun _ => rfl

 theorem polynomial_payload_count_mem_fp : polynomialPayloadCount ∈ FP :=
  CobhamFP_subset_FP polynomial_payload_count_cobham

 theorem polynomial_payload_count_length (input : List Bool) :
    (polynomialPayloadCount input).length ≤ 4*input.length+2 := by
  have hc := canonical_word_length (pairSnd (payloadCountState input))
  have hp := pairSnd_length_le (payloadCountState input)
  have hs := payload_count_clock_length input input
  change (canonicalWord (pairSnd (payloadCountState input))).length ≤ _
  unfold payloadCountState at hp hc ⊢
  omega

#print axioms polynomial_payload_count_mem_fp
end IV04.Paper.Computational
