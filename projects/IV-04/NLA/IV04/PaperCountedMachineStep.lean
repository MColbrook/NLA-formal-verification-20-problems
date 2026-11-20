module

public import NLA.IV04.PaperCountedMachineDefinitions
public import NLA.IV04.PaperCountedParserSemantics
public import NLA.IV04.PaperWordSubtractionPoly
public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperRationalParserSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem decrement_count_value (count : List Bool) :
    wordValue (decrementCount count)=wordValue count-1 := by
  simp [decrementCount,canonical_word_value,polynomial_word_sub_value,wordValue,bitValue]

theorem decrement_count_length (count : List Bool) :
    (decrementCount count).length ≤ count.length := by
  rw [decrementCount,canonical_word_eq_bits,polynomial_word_sub_value]
  simp only [wordValue,bitValue,ite_true,Nat.mul_zero,Nat.zero_add,Nat.size_eq_bits_len]
  have h := Nat.size_le_size (Nat.sub_le (wordValue count) 1)
  have hs : (wordValue count).size ≤ count.length := by
    simpa only [canonical_word_eq_bits,Nat.size_eq_bits_len] using canonical_word_length count
  exact h.trans hs

theorem counted_pack_cobham {n : ℕ}
    {count flag rest output : (Fin n → List Bool) → List Bool}
    (hc : Cobham count) (hf : Cobham flag) (hr : Cobham rest) (ho : Cobham output) :
    Cobham fun v => countedPack (count v) (flag v) (rest v) (output v) := by
  exact (Cobham.comp₂ Cobham.pairing hc (Cobham.comp₂ Cobham.pairing hf
    (Cobham.comp₂ Cobham.pairing hr ho))).of_eq fun _ => rfl

theorem decrement_count_cobham :
    Cobham fun v : Fin 1 → List Bool => decrementCount (v 0) := by
  have hs := Cobham.comp₂ polynomial_word_sub_cobham (Cobham.proj (0 : Fin 1)) (Cobham.const [true])
  exact (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hs).of_eq fun _ => rfl

theorem counted_step_cobham :
    Cobham fun v : Fin 1 → List Bool => countedStep (v 0) := by
  have hc : Cobham fun v : Fin 1 → List Bool => countedCount (v 0) := Cobham.fstBlockFn (.proj 0)
  have hf : Cobham fun v : Fin 1 → List Bool => countedFlag (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have hr : Cobham fun v : Fin 1 → List Bool => countedRest (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have ho : Cobham fun v : Fin 1 → List Bool => countedOutput (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have hp := Cobham.comp encoded_natural_parser_cobham fun _ : Fin 1 => hr
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn hp)
  have hout := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (Cobham.sndBlockFn hp)) ho
  have hd := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hc
  have hsuccess := counted_pack_cobham hd (Cobham.const [true]) ht hout
  have hfailure := counted_pack_cobham hc (Cobham.const [false]) hr ho
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.iteFn hn (Cobham.iteFn hf
    (Cobham.iteFn (Cobham.fstBlockFn hp) hsuccess hfailure) (Cobham.proj 0))
    (Cobham.proj 0)).of_eq fun _ => rfl

theorem counted_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => countedInitial (v 0) := by
  have hp := encoded_natural_parser_cobham
  have hc := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.fstBlockFn (Cobham.sndBlockFn hp)
  exact (counted_pack_cobham hc (Cobham.fstBlockFn hp)
    (Cobham.sndBlockFn (Cobham.sndBlockFn hp)) (Cobham.const [])).of_eq fun _ => rfl

#print axioms counted_step_cobham
end IV04.Paper.Computational
