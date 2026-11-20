module

public import NLA.IV04.PaperVertexSelectionBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem vertex_selection_state_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => vertexSelectionInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => vertexSelectionStep (v 0)
  let clockTwo : (Fin 2 → List Bool) → List Bool := fun v => v 0 ++ v 0
  let inputTwo : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    clockTwo v ++ inputTwo v ++ List.replicate 10 false
  have hi : Cobham initial := vertex_selection_initial_cobham
  have hs : Cobham step :=
    (Cobham.comp vertex_selection_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hc : Cobham clockTwo := Cobham.appendFn (.proj 0) (.proj 0)
  have ht : Cobham inputTwo := Cobham.appendFn (.proj 1) (.proj 1)
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn hc ht) (.const (List.replicate 10 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((vertexSelectionStep^[clock.length]) (vertexSelectionInitial (v 0))).length ≤ _
    have h := vertex_selection_initial_iterate_length clock.length (v 0)
    simp [ruler,clockTwo,inputTwo]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

set_option maxHeartbeats 2000000 in
theorem encoded_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedVertexSelection (v 0) := by
  have hc : Cobham fun v : Fin 1 → List Bool => vertexSelectionCount (vertexSelectionState (v 0)) :=
    Cobham.fstBlockFn vertex_selection_state_cobham
  have hf : Cobham fun v : Fin 1 → List Bool => vertexSelectionFlag (vertexSelectionState (v 0)) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn vertex_selection_state_cobham)
  have ht : Cobham fun v : Fin 1 → List Bool => vertexSelectionFields (vertexSelectionState (v 0)) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn vertex_selection_state_cobham))
  have hb : Cobham fun v : Fin 1 → List Bool => vertexSelectionChoices (vertexSelectionState (v 0)) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn vertex_selection_state_cobham)))
  have ho : Cobham fun v : Fin 1 → List Bool => vertexSelectionOutput (vertexSelectionState (v 0)) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn vertex_selection_state_cobham)))
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.comp₂ Cobham.pairing (Cobham.iteFn hn (.const [false]) hf)
    (Cobham.comp₂ Cobham.pairing ho (Cobham.comp₂ Cobham.pairing ht hb))).of_eq fun _ => rfl

theorem encoded_vertex_selection_mem_fp : encodedVertexSelection ∈ FP :=
  CobhamFP_subset_FP encoded_vertex_selection_cobham

#print axioms encoded_vertex_selection_mem_fp
end IV04.Paper.Computational
