module

public import NLA.IV04.PaperWordMultiplierDefinitions
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem polynomial_word_multiply_value (left right : List Bool) :
    wordValue (polynomialWordMultiply left right)=wordValue left*wordValue right := by
  induction left with
  | nil => simp [polynomialWordMultiply,wordValue]
  | cons b left ih =>
    cases b <;> simp [polynomialWordMultiply,polynomial_word_add_value,wordValue,bitValue,ih] <;> ring

theorem polynomial_word_multiply_length (left right : List Bool) :
    (polynomialWordMultiply left right).length ≤ left.length*(right.length+2) := by
  induction left with
  | nil => simp [polynomialWordMultiply]
  | cons b left ih =>
    have h := polynomial_word_add_length (if b then right else [])
      (false :: polynomialWordMultiply left right)
    have hb : (if b then right else []).length ≤ right.length := by cases b <;> simp
    simp only [polynomialWordMultiply,List.length_cons] at h ⊢
    nlinarith

theorem polynomial_word_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordMultiply (v 0) (v 1) := by
  let base : (Fin 1 → List Bool) → List Bool := fun _ => []
  let zero : (Fin 3 → List Bool) → List Bool :=
    fun v => polynomialWordAdd [] (false :: v 1)
  let one : (Fin 3 → List Bool) → List Bool :=
    fun v => polynomialWordAdd (v 2) (false :: v 1)
  let bound : (Fin 2 → List Bool) → List Bool := fun v => smash (v 0) (false :: false :: v 1)
  have ht : Cobham fun v : Fin 3 → List Bool => false :: v 1 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hg : Cobham base := .const []
  have hz : Cobham zero :=
    (Cobham.comp₂ polynomial_word_add_cobham (.const []) ht).of_eq fun v => by simp [zero]
  have ho : Cobham one :=
    (Cobham.comp₂ polynomial_word_add_cobham (.proj 2) ht).of_eq fun v => by simp [one]
  have hb : Cobham bound := by
    have hright : Cobham fun v : Fin 2 → List Bool => false :: false :: v 1 :=
      (Cobham.comp (.bit false) fun _ : Fin 1 =>
        (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl).of_eq fun _ => rfl
    exact (Cobham.comp₂ Cobham.smash (.proj 0) hright).of_eq fun v => by simp [bound]
  have hrec : ∀ (left : List Bool) (v : Fin 1 → List Bool),
      recNotation base zero one left v=polynomialWordMultiply left (v 0) := by
    intro left v
    induction left with
    | nil => rfl
    | cons b left ih =>
      cases b <;> simp [recNotation,base,zero,one,polynomialWordMultiply,ih] <;> rfl
  refine (Cobham.boundedRec hg hz ho hb ?_).of_eq fun v => ?_
  · intro left v
    rw [hrec]
    simpa [bound,smash_length] using polynomial_word_multiply_length left (v 0)
  · exact hrec (v 0) (Fin.tail v)

theorem encoded_word_multiply_mem_fp : encodedPolynomialWordMultiply ∈ FP := by
  have h := Cobham.comp₂ polynomial_word_multiply_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialWordMultiply])

theorem encoded_word_multiply_actual_polytime : encodedPolynomialWordMultiply ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordMultiply (Complexity.pair left right))=
      wordValue left*wordValue right := by
  refine ⟨encoded_word_multiply_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialWordMultiply] using polynomial_word_multiply_value left right

#print axioms encoded_word_multiply_actual_polytime
end IV04.Paper.Computational
