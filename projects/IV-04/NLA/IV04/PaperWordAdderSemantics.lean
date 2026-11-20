module

public import NLA.IV04.PaperWordAdderDefinitions
public import NLA.IV04.PaperBinaryArithmetic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem head_flag (bits : List Bool) : Complexity.bitAt [] bits=[firstBit bits] := by
  cases bits with
  | nil => rfl
  | cons b bits => cases b <;> rfl

theorem wordAdderStep_pack (left right output : List Bool) (carry : Bool) :
    wordAdderStep (adderPack left right [carry] output)=
      adderPack left.tail right.tail [carryBit (firstBit left) (firstBit right) carry]
        (sumBit (firstBit left) (firstBit right) carry :: output) := by
  simp only [wordAdderStep,adderLeft,adderRight,adderCarry,adderOutput,adderPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,head_flag]
  generalize firstBit left=a
  generalize firstBit right=b
  cases a <;> cases b <;> cases carry <;> rfl

theorem wordAdder_iterate_run (k : ℕ) (left right output : List Bool) (carry : Bool) :
    (wordAdderStep^[k]) (adderPack left right [carry] output)=adderRun k left right carry output := by
  induction k generalizing left right carry output with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,wordAdderStep_pack,ih]
    rfl

theorem adderRun_output (k : ℕ) (left right output : List Bool) (carry : Bool) :
    adderOutput (adderRun k left right carry output)=(rippleTrace k carry left right).reverse++output := by
  induction k generalizing left right carry output with
  | zero => simp [adderRun,rippleTrace,adderOutput,adderPack]
  | succ k ih =>
    simp only [adderRun,rippleTrace,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem adderRun_length (k : ℕ) (left right output : List Bool) (carry : Bool) :
    (adderRun k left right carry output).length ≤ 2*left.length+2*right.length+output.length+k+8 := by
  induction k generalizing left right carry output with
  | zero => simp [adderRun,adderPack,Complexity.pair_length]; omega
  | succ k ih =>
    simp only [adderRun]
    have h := ih left.tail right.tail
      (sumBit (firstBit left) (firstBit right) carry :: output)
      (carryBit (firstBit left) (firstBit right) carry)
    have hl : left.tail.length ≤ left.length := by cases left <;> simp
    have hr : right.tail.length ≤ right.length := by cases right <;> simp
    simp only [List.length_cons] at h
    omega

theorem ripple_trace_length (k : ℕ) (left right : List Bool) (carry : Bool) :
    (rippleTrace k carry left right).length=k := by
  induction k generalizing left right carry with
  | zero => rfl
  | succ k ih => simp [rippleTrace,ih]

theorem ripple_trace_zero (k : ℕ) : wordValue (rippleTrace k false [] [])=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rippleTrace,firstBit,sumBit,carryBit,wordValue,bitValue,ih]

theorem word_value_head_tail (bits : List Bool) :
    wordValue bits=2*wordValue bits.tail+bitValue (firstBit bits) := by
  cases bits <;> simp [wordValue,firstBit,bitValue]

theorem ripple_trace_value (k : ℕ) (left right : List Bool) (carry : Bool)
    (hk : left.length+right.length+1 ≤ k) :
    wordValue (rippleTrace k carry left right)=wordValue left+wordValue right+bitValue carry := by
  induction k generalizing left right carry with
  | zero => omega
  | succ k ih =>
    by_cases hz : left=[] ∧ right=[]
    · obtain ⟨rfl,rfl⟩ := hz
      cases carry <;> simp [rippleTrace,firstBit,sumBit,carryBit,wordValue,bitValue,ripple_trace_zero]
    · have ht : left.tail.length+right.tail.length+1 ≤ k := by
        cases left <;> cases right <;> simp_all <;> omega
      rw [rippleTrace,wordValue,ih _ _ _ ht]
      have hf := full_adder_identity (firstBit left) (firstBit right) carry
      have hl := word_value_head_tail left
      have hr := word_value_head_tail right
      omega

theorem polynomial_word_add_trace (left right : List Bool) :
    polynomialWordAdd left right=rippleTrace (left.length+right.length+1) false left right := by
  simp [polynomialWordAdd,wordAdder_iterate_run,adderRun_output]

theorem polynomial_word_add_value (left right : List Bool) :
    wordValue (polynomialWordAdd left right)=wordValue left+wordValue right := by
  rw [polynomial_word_add_trace]
  simpa [bitValue] using ripple_trace_value (left.length+right.length+1) left right false (by omega)

theorem polynomial_word_add_length (left right : List Bool) :
    (polynomialWordAdd left right).length=left.length+right.length+1 := by
  rw [polynomial_word_add_trace,ripple_trace_length]

#print axioms polynomial_word_add_value
end IV04.Paper.Computational
