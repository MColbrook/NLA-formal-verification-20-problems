module

public import NLA.IV04.PaperSATVariableMarkersBounds
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
 theorem variable_marker_pack_cobham {n : ℕ}
    {index bound query output : (Fin n → List Bool) → List Bool}
    (hi : Cobham index) (hb : Cobham bound) (hq : Cobham query) (ho : Cobham output) :
    Cobham fun v => variableMarkerPack (index v) (bound v) (query v) (output v) :=
  (Cobham.comp₂ Cobham.pairing hi (Cobham.comp₂ Cobham.pairing hb
    (Cobham.comp₂ Cobham.pairing hq ho))).of_eq fun _ => rfl
 theorem variable_marker_digit_cobham :
    Cobham fun v : Fin 2 → List Bool => variableMarkerDigit (v 0) (v 1) := by
  exact (Cobham.iteFn (Cobham.comp₂ literal_match_flag_cobham
    (Cobham.comp₂ Cobham.pairing (.proj 0) (.const [false]))
    (Cobham.comp₂ Cobham.pairing (.proj 1) (.const [false]))) (.const [true]) (.const [])).of_eq fun _ => rfl
 theorem variable_marker_step_cobham :
    Cobham fun v : Fin 1 → List Bool => variableMarkerStep (v 0) := by
  have hi := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hq := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hn := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.comp₂ polynomial_word_add_cobham hi (.const [true])
  have hd := Cobham.comp₂ variable_marker_digit_cobham hi hq
  exact (Cobham.iteFn (Cobham.notFn (Cobham.comp₂ polynomial_word_le_cobham hb hi))
    (variable_marker_pack_cobham hn hb hq (Cobham.comp₂ Cobham.pairing hd ho)) (.proj 0)).of_eq fun _ => rfl
 theorem variable_marker_state_cobham :
    Cobham fun v : Fin 1 → List Bool => variableMarkerState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v =>
    variableMarkerPack [] (pairFst (pairSnd (v 0))) (pairSnd (pairSnd (v 0))) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => variableMarkerStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 6 false ++ Complexity.smash (v 0) (List.replicate 8 false)
  have hi : Cobham initial := variable_marker_pack_cobham (.const [])
    (Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0)))
    (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))) (.const [])
  have hs : Cobham step :=
    (Cobham.comp variable_marker_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 6 false)))
    (Cobham.comp₂ Cobham.smash (.proj 0) (.const (List.replicate 8 false)))
  have hbound : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((variableMarkerStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd (v 0))) (pairSnd (pairSnd (v 0))) [])).length ≤ _
    have h := variable_marker_clock_length clock (v 0)
    simp [ruler,Complexity.smash_length];omega
  have hit := Cobham.iterFn hi hs hr hbound
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => false::pairFst (v 0),fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · exact (Cobham.comp (Cobham.bit false) fun _ : Fin 1 => Cobham.fstBlockFn (.proj 0)).of_eq fun _ => rfl
    · exact (Cobham.proj 0).of_eq fun _ => rfl
  exact (Cobham.comp hit ha).of_eq fun v => by simp [variableMarkerState,initial,step,args]
 theorem polynomial_sat_variable_markers_mem_fp : polynomialSATVariableMarkers ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn (Cobham.sndBlockFn
    (Cobham.sndBlockFn variable_marker_state_cobham))).of_eq fun _ => rfl)
#print axioms polynomial_sat_variable_markers_mem_fp
end IV04.Paper.Computational
