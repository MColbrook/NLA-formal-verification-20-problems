module

public import NLA.IV04.PaperWordComparisonPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_word_comparison_step_pack (left right : List Bool) (flag : Bool) :
    wordComparisonStep (comparisonPack left right [flag])=
      comparisonPack left.tail right.tail [comparisonBit (firstBit left) (firstBit right) flag] := by
  exact word_comparison_step_pack left right flag

theorem verified_word_comparison_iterate_run (k : ℕ) (left right : List Bool) (flag : Bool) :
    (wordComparisonStep^[k]) (comparisonPack left right [flag])=comparisonRun k left right flag := by
  exact word_comparison_iterate_run k left right flag

theorem verified_comparison_run_flag (k : ℕ) (left right : List Bool) (flag : Bool) :
    comparisonFlag (comparisonRun k left right flag)=[comparisonTrace k flag left right] := by
  exact comparison_run_flag k left right flag

theorem verified_comparison_run_length (k : ℕ) (left right : List Bool) (flag : Bool) :
    (comparisonRun k left right flag).length ≤ 2*left.length+2*right.length+5 := by
  exact comparison_run_length k left right flag

theorem verified_comparison_trace_zero (k : ℕ) (flag : Bool) :
    comparisonTrace k flag [] []=flag := by
  exact comparison_trace_zero k flag

theorem verified_comparison_trace_value (k : ℕ) (left right : List Bool) (flag : Bool)
    (hk : left.length+right.length ≤ k) :
    comparisonTrace k flag left right=true ↔
      wordValue left<wordValue right ∨ (wordValue left=wordValue right ∧ flag=true) := by
  exact comparison_trace_value k left right flag hk

theorem verified_polynomial_word_le_value (left right : List Bool) :
    polynomialWordLe left right=[decide (wordValue left ≤ wordValue right)] := by
  exact polynomial_word_le_value left right

theorem verified_comparison_pack_cobham {n : ℕ}
    {left right flag : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) (hf : Cobham flag) :
    Cobham fun v => comparisonPack (left v) (right v) (flag v) := by
  exact comparison_pack_cobham hl hr hf

theorem verified_word_comparison_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordComparisonStep (v 0) := by
  exact word_comparison_step_cobham

theorem verified_word_comparison_state_cobham :
    Cobham fun v : Fin 2 → List Bool =>
      (wordComparisonStep^[(v 0).length+(v 1).length]) (comparisonPack (v 0) (v 1) [true]) := by
  exact word_comparison_state_cobham

theorem verified_polynomial_word_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordLe (v 0) (v 1) := by
  exact polynomial_word_le_cobham

theorem verified_encoded_word_le_mem_fp : encodedPolynomialWordLe ∈ FP := by
  exact encoded_word_le_mem_fp

theorem verified_encoded_word_le_actual_polytime : encodedPolynomialWordLe ∈ FP ∧
    ∀ left right, encodedPolynomialWordLe (Complexity.pair left right)=
      [decide (wordValue left ≤ wordValue right)] := by
  exact encoded_word_le_actual_polytime

#print axioms IV04.Paper.Computational.verified_word_comparison_step_pack
#print axioms IV04.Paper.Computational.verified_word_comparison_iterate_run
#print axioms IV04.Paper.Computational.verified_comparison_run_flag
#print axioms IV04.Paper.Computational.verified_comparison_run_length
#print axioms IV04.Paper.Computational.verified_comparison_trace_zero
#print axioms IV04.Paper.Computational.verified_comparison_trace_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_le_value
#print axioms IV04.Paper.Computational.verified_comparison_pack_cobham
#print axioms IV04.Paper.Computational.verified_word_comparison_step_cobham
#print axioms IV04.Paper.Computational.verified_word_comparison_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_word_le_cobham
#print axioms IV04.Paper.Computational.verified_encoded_word_le_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_word_le_actual_polytime
end IV04.Paper.Computational
