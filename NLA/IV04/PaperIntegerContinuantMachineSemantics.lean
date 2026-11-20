module

public import NLA.IV04.PaperIntegerContinuantMachinePoly
public import NLA.IV04.PaperIntegerContinuantMachineReference
public import NLA.IV04.PaperCountedOutputSemantics
public import NLA.IV04.PaperWordListProductSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem integer_continuant_iterate_nil (k : ℕ) (previous before : List Bool) :
    (integerContinuantStep^[k]) (integerContinuantPack [] previous before)=integerContinuantPack [] previous before := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,integer_continuant_step_pack]; simp

theorem integer_continuant_iterate_code (k : ℕ) (rows : List (List Bool))
    (previous before : List Bool) (h : rows.length ≤ k) :
    (integerContinuantStep^[k]) (integerContinuantPack (payloadListCode rows) previous before)=
      integerContinuantPack [] (integerContinuantWordRun rows previous before).1
        (integerContinuantWordRun rows previous before).2 := by
  induction k generalizing rows previous before with
  | zero =>
    have he : rows=[] := by cases rows <;> simp_all
    simp [he,payloadListCode,integerContinuantWordRun]
  | succ k ih =>
    cases rows with
    | nil => simp [payloadListCode,integerContinuantWordRun,integer_continuant_iterate_nil]
    | cons row rows =>
      have ht : rows.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,integer_continuant_step_pack]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,pairFst_pair,pairSnd_pair,integerContinuantWordRun]
      exact ih rows (integerContinuantNext row previous before) previous ht

theorem integer_continuant_code (rows : List (List Bool)) :
    polynomialIntegerContinuant (payloadListCode rows)=(integerContinuantWordRun rows [false,true] [false]).1 := by
  have h := integer_continuant_iterate_code (payloadListCode rows).length rows [false,true] [false]
    (payload_list_count_length rows)
  simpa only [polynomialIntegerContinuant,integerContinuantState,integerContinuantInitial,
    integerContinuantPrevious,integerContinuantPack,pairFst_pair,pairSnd_pair]
    using congrArg integerContinuantPrevious h

theorem integer_continuant_word_run_value (rows : List (List Bool)) (previous before : List Bool) :
    (signedWordValue (integerContinuantWordRun rows previous before).1,
      signedWordValue (integerContinuantWordRun rows previous before).2)=
      integerContinuantNumericRun (rows.map integerContinuantRowValue) (signedWordValue previous) (signedWordValue before) := by
  induction rows generalizing previous before with
  | nil => rfl
  | cons row rows ih =>
    simp only [integerContinuantWordRun,List.map_cons,integerContinuantNumericRun]
    rw [ih,integer_continuant_next_value]
    rfl

theorem integer_continuant_code_value (rows : List (List Bool)) :
    signedWordValue (polynomialIntegerContinuant (payloadListCode rows))=
      (integerContinuantNumericRun (rows.map integerContinuantRowValue) 1 0).1 := by
  rw [integer_continuant_code]
  have h := congrArg Prod.fst (integer_continuant_word_run_value rows [false,true] [false])
  exact h

theorem integer_continuant_numeric_run_append (rows more : List (ℤ × ℤ × ℤ)) (previous before : ℤ) :
    integerContinuantNumericRun (rows++more) previous before=
      integerContinuantNumericRun more (integerContinuantNumericRun rows previous before).1
        (integerContinuantNumericRun rows previous before).2 := by
  induction rows generalizing previous before with
  | nil => rfl
  | cons row rows ih => simp only [List.cons_append,integerContinuantNumericRun]; exact ih _ _

theorem integer_continuant_numeric_rows_value (a lower upper : ℕ → ℤ) (n : ℕ) :
    integerContinuantNumericRun (integerContinuantNumericRows a lower upper n) 1 0=
      (integerContinuantValue a lower upper n,if n=0 then 0 else integerContinuantValue a lower upper (n-1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : integerContinuantNumericRows a lower upper (n+1)=
        integerContinuantNumericRows a lower upper n ++ [(a n,lower n,upper (n-1))] := by
      simp [integerContinuantNumericRows,List.range_succ,List.map_append]
    rw [he,integer_continuant_numeric_run_append,ih]
    cases n with
    | zero => simp [integerContinuantNumericRun,integerContinuantValue]
    | succ n => simp [integerContinuantNumericRun,integerContinuantValue]

theorem integer_continuant_actual_polytime : polynomialIntegerContinuant ∈ FP ∧
    ∀ rows : List (List Bool),
      signedWordValue (polynomialIntegerContinuant (payloadListCode rows))=
        (integerContinuantNumericRun (rows.map integerContinuantRowValue) 1 0).1 :=
  ⟨polynomial_integer_continuant_mem_fp,integer_continuant_code_value⟩

#print axioms integer_continuant_actual_polytime
end IV04.Paper.Computational
