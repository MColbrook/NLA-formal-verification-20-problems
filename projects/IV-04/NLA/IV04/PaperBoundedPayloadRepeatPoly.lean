module

public import NLA.IV04.PaperBoundedPayloadRepeatBounds
public import NLA.IV04.PaperSATLiteralDigitsPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
 theorem bounded_payload_repeat_step_cobham :
    Cobham fun v : Fin 1 → List Bool => boundedPayloadRepeatStep (v 0) := by
  have hi := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hb := sat_literal_cobham_fst _ (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0))
  have hq := sat_literal_cobham_fst _ (sat_literal_cobham_snd _
    (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
  have ho := sat_literal_cobham_snd _ (sat_literal_cobham_snd _
    (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
  have hn := sat_literal_cobham_unary canonicalWord canonical_word_cobham _
    (sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham
      _ (fun _ : Fin 1 → List Bool => [true]) hi (.const [true]))
  exact (Cobham.iteFn
    (Cobham.notFn (sat_literal_cobham_binary polynomialWordLe polynomial_word_le_cobham _ _ hb hi))
    (variable_marker_pack_cobham hn hb hq (sat_literal_cobham_binary pair Cobham.pairing _ _ hq ho))
    (.proj 0)).of_eq fun _ => rfl
 theorem bounded_payload_repeat_state_cobham :
    Cobham fun v : Fin 1 → List Bool => boundedPayloadRepeatState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v =>
    variableMarkerPack [] (pairFst (pairSnd (v 0))) (pairSnd (pairSnd (v 0))) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => boundedPayloadRepeatStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 6 false ++
      Complexity.smash (v 0) (v 1 ++ v 1 ++ List.replicate 8 false)
  have hi : Cobham initial := variable_marker_pack_cobham (.const [])
    (Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0)))
    (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))) (.const [])
  have hs : Cobham step :=
    sat_literal_cobham_unary boundedPayloadRepeatStep bounded_payload_repeat_step_cobham
      (fun v : Fin 2 → List Bool => v 0) (.proj 0)
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 6 false)))
    (Cobham.comp₂ Cobham.smash (.proj 0)
      (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 8 false))))
  have hbound : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((boundedPayloadRepeatStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd (v 0))) (pairSnd (pairSnd (v 0))) [])).length ≤ _
    have h := bounded_payload_repeat_clock_length clock (v 0)
    simp [ruler,Complexity.smash_length]
    nlinarith [h]
  have hit := Cobham.iterFn hi hs hr hbound
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => false::pairFst (v 0),fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · exact (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => Cobham.fstBlockFn (.proj 0)).of_eq fun _ => rfl
    · exact (Cobham.proj 0).of_eq fun _ => rfl
  exact (Cobham.comp hit ha).of_eq fun v => by simp [boundedPayloadRepeatState,initial,step,args]
 theorem polynomial_bounded_payload_repeat_mem_fp : polynomialBoundedPayloadRepeat ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn (Cobham.sndBlockFn
    (Cobham.sndBlockFn bounded_payload_repeat_state_cobham))).of_eq fun _ => rfl)
#print axioms polynomial_bounded_payload_repeat_mem_fp
end IV04.Paper.Computational
