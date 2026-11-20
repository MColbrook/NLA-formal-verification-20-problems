module

public import NLA.IV04.PaperLengthWordDefinitions
public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem raw_length_word_value (input : List Bool) : wordValue (rawLengthWord input)=input.length := by
  induction input with
  | nil => rfl
  | cons b bits ih => simp [rawLengthWord,polynomial_word_add_value,wordValue,bitValue,ih] <;> omega

theorem raw_length_word_length (input : List Bool) : (rawLengthWord input).length ≤ 2*input.length := by
  induction input with
  | nil => rfl
  | cons b bits ih => simp only [rawLengthWord,polynomial_word_add_length,List.length_cons,List.length_nil]; omega

theorem input_length_word_value (input : List Bool) : wordValue (inputLengthWord input)=input.length := by
  simp [inputLengthWord,canonical_word_value,raw_length_word_value]

theorem input_length_word_exact (input : List Bool) : inputLengthWord input=input.length.bits := by
  simp [inputLengthWord,canonical_word_eq_bits,raw_length_word_value]

theorem raw_length_word_cobham :
    Cobham fun v : Fin 1 → List Bool => rawLengthWord (v 0) := by
  let base : (Fin 0 → List Bool) → List Bool := fun _ => []
  let step : (Fin 2 → List Bool) → List Bool := fun v => polynomialWordAdd [true] (v 1)
  let bound : (Fin 1 → List Bool) → List Bool := fun v => v 0 ++ v 0
  have hg : Cobham base := .const []
  have hs : Cobham step :=
    (Cobham.comp₂ polynomial_word_add_cobham (Cobham.const [true]) (Cobham.proj 1)).of_eq fun _ => rfl
  have hb : Cobham bound := Cobham.appendFn (.proj 0) (.proj 0)
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation base step step bits v=rawLengthWord bits := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih => cases b <;> simp [recNotation,base,step,rawLengthWord,ih]
  refine (Cobham.boundedRec hg hs hs hb ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec]
    have h := raw_length_word_length bits
    simpa [bound,List.length_append,two_mul] using h
  · exact hrec (v 0) (Fin.tail v)

theorem input_length_word_cobham :
    Cobham fun v : Fin 1 → List Bool => inputLengthWord (v 0) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 => raw_length_word_cobham).of_eq fun _ => rfl

theorem input_length_word_mem_fp : inputLengthWord ∈ FP :=
  CobhamFP_subset_FP input_length_word_cobham

theorem input_length_actual_polytime : inputLengthWord ∈ FP ∧
    ∀ input, inputLengthWord input=input.length.bits :=
  ⟨input_length_word_mem_fp,input_length_word_exact⟩

#print axioms input_length_actual_polytime
end IV04.Paper.Computational
