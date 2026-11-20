module

public import NLA.IV04.PaperWordComparisonSemantics
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem comparison_pack_cobham {n : ℕ}
    {left right flag : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) (hf : Cobham flag) :
    Cobham fun v => comparisonPack (left v) (right v) (flag v) := by
  exact (Cobham.comp₂ Cobham.pairing hl (Cobham.comp₂ Cobham.pairing hr hf)).of_eq fun _ => rfl

theorem word_comparison_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordComparisonStep (v 0) := by
  have hl : Cobham fun v : Fin 1 → List Bool => comparisonLeft (v 0) :=
    Cobham.fstBlockFn (.proj 0)
  have hr : Cobham fun v : Fin 1 → List Bool => comparisonRight (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have hf : Cobham fun v : Fin 1 → List Bool => comparisonFlag (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))
  have ha := Cobham.headFlagFn hl
  have hb := Cobham.headFlagFn hr
  have hc := Cobham.iteFn (xor_flag_cobham ha hb) (Cobham.andFn (Cobham.notFn ha) hb) hf
  exact (comparison_pack_cobham (Cobham.tailFn hl) (Cobham.tailFn hr) hc).of_eq fun _ => rfl

theorem word_comparison_state_cobham :
    Cobham fun v : Fin 2 → List Bool =>
      (wordComparisonStep^[(v 0).length+(v 1).length]) (comparisonPack (v 0) (v 1) [true]) := by
  let initial : (Fin 2 → List Bool) → List Bool :=
    fun v => comparisonPack (v 0) (v 1) [true]
  let step : (Fin 3 → List Bool) → List Bool := fun v => wordComparisonStep (v 0)
  let ruler : (Fin 3 → List Bool) → List Bool :=
    fun v => v 1 ++ v 1 ++ v 2 ++ v 2 ++ List.replicate 5 false
  have he : Cobham initial := comparison_pack_cobham (.proj 0) (.proj 1) (.const [true])
  have hs : Cobham step :=
    (Cobham.comp word_comparison_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hj : Cobham ruler :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
      (Cobham.appendFn (.proj 1) (.proj 1)) (.proj 2)) (.proj 2))
      (.const (List.replicate 5 false))
  have hbound : ∀ (clock : List Bool) (v : Fin 2 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((wordComparisonStep^[clock.length]) (comparisonPack (v 0) (v 1) [true])).length ≤ _
    rw [word_comparison_iterate_run]
    have h := comparison_run_length clock.length (v 0) (v 1) true
    change (comparisonRun clock.length (v 0) (v 1) true).length ≤
      ((v 0) ++ (v 0) ++ (v 1) ++ (v 1) ++ List.replicate 5 false).length
    simp only [List.length_append,List.length_replicate]
    omega
  have hi := Cobham.iterFn he hs hj hbound
  let arguments : Fin 3 → (Fin 2 → List Bool) → List Bool :=
    ![fun v => v 0 ++ v 1,fun v => v 0,fun v => v 1]
  have hargs : ∀ i, Cobham (arguments i) := by
    intro i
    fin_cases i
    · simpa [arguments] using Cobham.appendFn (Cobham.proj (0 : Fin 2)) (Cobham.proj 1)
    · simpa [arguments] using (Cobham.proj 0 : Cobham fun v : Fin 2 → List Bool => v 0)
    · simpa [arguments] using (Cobham.proj 1 : Cobham fun v : Fin 2 → List Bool => v 1)
  refine (Cobham.comp hi hargs).of_eq fun v => ?_
  simp [arguments,initial,step,List.length_append]

theorem polynomial_word_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordLe (v 0) (v 1) :=
  (Cobham.sndBlockFn (Cobham.sndBlockFn word_comparison_state_cobham)).of_eq fun _ => rfl

theorem encoded_word_le_mem_fp : encodedPolynomialWordLe ∈ FP := by
  have h := Cobham.comp₂ polynomial_word_le_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialWordLe])

theorem encoded_word_le_actual_polytime : encodedPolynomialWordLe ∈ FP ∧
    ∀ left right, encodedPolynomialWordLe (Complexity.pair left right)=
      [decide (wordValue left ≤ wordValue right)] := by
  refine ⟨encoded_word_le_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialWordLe] using polynomial_word_le_value left right

#print axioms encoded_word_le_actual_polytime
end IV04.Paper.Computational
