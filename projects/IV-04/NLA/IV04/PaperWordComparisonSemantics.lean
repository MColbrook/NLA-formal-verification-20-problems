module

public import NLA.IV04.PaperWordComparisonDefinitions
public import NLA.IV04.PaperWordAdderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem word_comparison_step_pack (left right : List Bool) (flag : Bool) :
    wordComparisonStep (comparisonPack left right [flag])=
      comparisonPack left.tail right.tail [comparisonBit (firstBit left) (firstBit right) flag] := by
  simp only [wordComparisonStep,comparisonLeft,comparisonRight,comparisonFlag,comparisonPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,head_flag]
  generalize firstBit left=a
  generalize firstBit right=b
  cases a <;> cases b <;> cases flag <;> rfl

theorem word_comparison_iterate_run (k : ℕ) (left right : List Bool) (flag : Bool) :
    (wordComparisonStep^[k]) (comparisonPack left right [flag])=comparisonRun k left right flag := by
  induction k generalizing left right flag with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply,word_comparison_step_pack,ih]; rfl

theorem comparison_run_flag (k : ℕ) (left right : List Bool) (flag : Bool) :
    comparisonFlag (comparisonRun k left right flag)=[comparisonTrace k flag left right] := by
  induction k generalizing left right flag with
  | zero => simp [comparisonRun,comparisonFlag,comparisonPack,comparisonTrace]
  | succ k ih => simp [comparisonRun,comparisonTrace,ih]

theorem comparison_run_length (k : ℕ) (left right : List Bool) (flag : Bool) :
    (comparisonRun k left right flag).length ≤ 2*left.length+2*right.length+5 := by
  induction k generalizing left right flag with
  | zero => simp [comparisonRun,comparisonPack,Complexity.pair_length]; omega
  | succ k ih =>
    simp only [comparisonRun]
    have h := ih left.tail right.tail (comparisonBit (firstBit left) (firstBit right) flag)
    have hl : left.tail.length ≤ left.length := by cases left <;> simp
    have hr : right.tail.length ≤ right.length := by cases right <;> simp
    omega

theorem comparison_trace_zero (k : ℕ) (flag : Bool) :
    comparisonTrace k flag [] []=flag := by
  induction k with
  | zero => rfl
  | succ k ih => simp [comparisonTrace,firstBit,comparisonBit,ih]

theorem comparison_trace_value (k : ℕ) (left right : List Bool) (flag : Bool)
    (hk : left.length+right.length ≤ k) :
    comparisonTrace k flag left right=true ↔
      wordValue left<wordValue right ∨ (wordValue left=wordValue right ∧ flag=true) := by
  induction k generalizing left right flag with
  | zero =>
    have hl : left=[] := by cases left <;> simp_all
    have hr : right=[] := by cases right <;> simp_all
    simp [hl,hr,comparisonTrace,wordValue]
  | succ k ih =>
    by_cases hz : left=[] ∧ right=[]
    · obtain ⟨rfl,rfl⟩ := hz
      simp [comparison_trace_zero,wordValue]
    · have ht : left.tail.length+right.tail.length ≤ k := by
        cases left <;> cases right <;> simp_all <;> omega
      rw [comparisonTrace,ih _ _ _ ht]
      have hl := word_value_head_tail left
      have hr := word_value_head_tail right
      generalize ha : firstBit left=a at *
      generalize hb : firstBit right=b at *
      cases a <;> cases b <;> cases flag <;> simp_all [comparisonBit,bitValue] <;> omega

theorem polynomial_word_le_value (left right : List Bool) :
    polynomialWordLe left right=[decide (wordValue left ≤ wordValue right)] := by
  simp only [polynomialWordLe,word_comparison_iterate_run,comparison_run_flag]
  have h := comparison_trace_value (left.length+right.length) left right true (by omega)
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [h]
  simp only [eq_self_iff_true,and_true]
  omega

#print axioms polynomial_word_le_value
end IV04.Paper.Computational
