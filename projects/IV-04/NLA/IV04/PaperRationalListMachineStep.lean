module

public import NLA.IV04.PaperRationalListParserDefinitions
public import NLA.IV04.PaperRationalParserPoly
public import NLA.IV04.PaperCountedMachineStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem rational_list_step_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListStep (v 0) := by
  have hc : Cobham fun v : Fin 1 → List Bool => countedCount (v 0) := Cobham.fstBlockFn (.proj 0)
  have hf : Cobham fun v : Fin 1 → List Bool => countedFlag (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have hr : Cobham fun v : Fin 1 → List Bool => countedRest (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have ho : Cobham fun v : Fin 1 → List Bool => countedOutput (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have hp := Cobham.comp encoded_rational_parser_cobham fun _ : Fin 1 => hr
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn hp)
  have hout := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (Cobham.sndBlockFn hp)) ho
  have hd := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hc
  have hsuccess := counted_pack_cobham hd (Cobham.const [true]) ht hout
  have hfailure := counted_pack_cobham hc (Cobham.const [false]) hr ho
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.iteFn hn (Cobham.iteFn hf
    (Cobham.iteFn (Cobham.fstBlockFn hp) hsuccess hfailure) (Cobham.proj 0))
    (Cobham.proj 0)).of_eq fun _ => rfl

theorem rational_list_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListInitial (v 0) := by
  have hc := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  exact (counted_pack_cobham hc (Cobham.const [true])
    (Cobham.sndBlockFn (Cobham.proj 0)) (Cobham.const [])).of_eq fun _ => rfl

#print axioms rational_list_step_cobham
end IV04.Paper.Computational
