module

public import NLA.IV04.PaperPayloadNaturalOutputBounds
public import NLA.IV04.PaperWordListSumPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem payload_natural_output_step_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadNaturalOutputStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have ho := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.comp canonical_word_code_cobham fun _ : Fin 1 => Cobham.fstBlockFn hr
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr) (Cobham.appendFn ho hc)
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (.proj 0)).of_eq fun _ => rfl

theorem payload_natural_output_state_cobham :
    Cobham fun v : Fin 1 → List Bool => payloadNaturalOutputState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => payloadNaturalOutputStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 0 ++ v 1 ++ v 1 ++ List.replicate 2 false
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [])
  have hs : Cobham step :=
    (Cobham.comp payload_natural_output_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 1)) (.proj 1)) (.const (List.replicate 2 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((payloadNaturalOutputStep^[clock.length]) (pair (v 0) [])).length ≤ _
    have h := payload_natural_output_iterate_length clock.length (v 0) []
    simp only [List.length_nil] at h
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_payload_naturals_mem_fp : polynomialPayloadNaturals ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn payload_natural_output_state_cobham).of_eq fun _ => rfl)

#print axioms polynomial_payload_naturals_mem_fp
end IV04.Paper.Computational
