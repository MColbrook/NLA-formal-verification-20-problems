module

public import NLA.IV04.PaperBinaryArithmetic
public import NLA.IV04.Complexitylib.Classes.P.Cobham
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem increment_word_cobham :
    Complexity.Cobham fun v : Fin 1 → List Bool => incrementWord true (v 0) := by
  open Complexity Complexity.Cobham in
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation (fun _ : Fin 0 → List Bool => [true])
        (fun w : Fin 2 → List Bool => true :: w 0)
        (fun w : Fin 2 → List Bool => false :: w 1) bits v = incrementWord true bits := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih => cases b <;> simp [recNotation,incrementWord,ih]
  have hg : Complexity.Cobham fun _ : Fin 0 → List Bool => [true] :=
    Complexity.Cobham.const [true]
  have hzero : Complexity.Cobham fun w : Fin 2 → List Bool => true :: w 0 :=
    (Complexity.Cobham.comp (.bit true) fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hone : Complexity.Cobham fun w : Fin 2 → List Bool => false :: w 1 :=
    (Complexity.Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hbound : Complexity.Cobham fun w : Fin 1 → List Bool => false :: w 0 :=
    (Complexity.Cobham.comp (.bit false) fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  refine (Complexity.Cobham.boundedRec hg hzero hone hbound ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec]
    exact increment_word_length bits true
  · exact hrec (v 0) (Fin.tail v)

theorem increment_word_mem_fp :
    (fun bits : List Bool => incrementWord true bits) ∈ Complexity.FP := by
  exact Complexity.CobhamFP_subset_FP increment_word_cobham

theorem increment_word_actual_polytime :
    (fun bits : List Bool => incrementWord true bits) ∈ Complexity.FP ∧
      ∀ bits, wordValue (incrementWord true bits)=wordValue bits+1 ∧
        (incrementWord true bits).length ≤ bits.length+1 := by
  refine ⟨increment_word_mem_fp,?_⟩
  intro bits
  exact ⟨by simpa [bitValue] using increment_word_value bits true,
    increment_word_length bits true⟩

#print axioms increment_word_actual_polytime
end IV04.Paper.Computational
