module

public import NLA.IV04.PaperWordSubtractionSemantics
public import NLA.IV04.PaperWordComparisonPoly
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem word_complement_cobham :
    Cobham fun v : Fin 1 → List Bool => (v 0).map Bool.not := by
  let base : (Fin 0 → List Bool) → List Bool := fun _ => []
  let zero : (Fin 2 → List Bool) → List Bool := fun v => true :: v 1
  let one : (Fin 2 → List Bool) → List Bool := fun v => false :: v 1
  have hg : Cobham base := .const []
  have hz : Cobham zero :=
    (Cobham.comp (.bit true) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have ho : Cobham one :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation base zero one bits v=bits.map Bool.not := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih => cases b <;> simp [recNotation,base,zero,one,ih]
  refine (Cobham.boundedRec hg hz ho (Cobham.proj 0) ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec]
    simp
  · exact hrec (v 0) (Fin.tail v)

theorem raw_word_difference_cobham :
    Cobham fun v : Fin 2 → List Bool => rawWordDifference (v 0) (v 1) := by
  have hr : Cobham fun v : Fin 2 → List Bool => false :: (v 0 ++ v 1) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => Cobham.appendFn (.proj 0) (.proj 1)).of_eq fun _ => rfl
  have hn := Cobham.comp word_complement_cobham fun _ : Fin 1 => Cobham.padFn hr (.proj 1)
  have hi := Cobham.comp₂ polynomial_word_add_cobham (Cobham.const [true]) hn
  have hs := Cobham.comp₂ polynomial_word_add_cobham (Cobham.proj (0 : Fin 2)) hi
  exact (Cobham.takeFn hr hs).of_eq fun v => by simp [rawWordDifference]

theorem polynomial_word_sub_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordSub (v 0) (v 1) := by
  have hc := Cobham.comp₂ polynomial_word_le_cobham (Cobham.proj (1 : Fin 2)) (Cobham.proj 0)
  exact (Cobham.iteFn hc raw_word_difference_cobham (Cobham.const [])).of_eq fun v => by
    simp [polynomialWordSub]

theorem encoded_word_sub_mem_fp : encodedPolynomialWordSub ∈ FP := by
  have h := Cobham.comp₂ polynomial_word_sub_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialWordSub])

theorem encoded_word_sub_actual_polytime : encodedPolynomialWordSub ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordSub (Complexity.pair left right))=
      wordValue left-wordValue right := by
  refine ⟨encoded_word_sub_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialWordSub] using polynomial_word_sub_value left right

#print axioms encoded_word_sub_actual_polytime
end IV04.Paper.Computational
