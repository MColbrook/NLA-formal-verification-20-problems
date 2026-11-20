module

public import NLA.IV04.PaperWordMultiplierPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_head_flag (bits : List Bool) : Complexity.bitAt [] bits=[firstBit bits] := by
  exact head_flag bits

theorem verified_wordAdderStep_pack (left right output : List Bool) (carry : Bool) :
    wordAdderStep (adderPack left right [carry] output)=
      adderPack left.tail right.tail [carryBit (firstBit left) (firstBit right) carry]
        (sumBit (firstBit left) (firstBit right) carry :: output) := by
  exact wordAdderStep_pack left right output carry

theorem verified_wordAdder_iterate_run (k : ℕ) (left right output : List Bool) (carry : Bool) :
    (wordAdderStep^[k]) (adderPack left right [carry] output)=adderRun k left right carry output := by
  exact wordAdder_iterate_run k left right output carry

theorem verified_adderRun_output (k : ℕ) (left right output : List Bool) (carry : Bool) :
    adderOutput (adderRun k left right carry output)=(rippleTrace k carry left right).reverse++output := by
  exact adderRun_output k left right output carry

theorem verified_adderRun_length (k : ℕ) (left right output : List Bool) (carry : Bool) :
    (adderRun k left right carry output).length ≤ 2*left.length+2*right.length+output.length+k+8 := by
  exact adderRun_length k left right output carry

theorem verified_ripple_trace_length (k : ℕ) (left right : List Bool) (carry : Bool) :
    (rippleTrace k carry left right).length=k := by
  exact ripple_trace_length k left right carry

theorem verified_ripple_trace_zero (k : ℕ) : wordValue (rippleTrace k false [] [])=0 := by
  exact ripple_trace_zero k

theorem verified_word_value_head_tail (bits : List Bool) :
    wordValue bits=2*wordValue bits.tail+bitValue (firstBit bits) := by
  exact word_value_head_tail bits

theorem verified_ripple_trace_value (k : ℕ) (left right : List Bool) (carry : Bool)
    (hk : left.length+right.length+1 ≤ k) :
    wordValue (rippleTrace k carry left right)=wordValue left+wordValue right+bitValue carry := by
  exact ripple_trace_value k left right carry hk

theorem verified_polynomial_word_add_trace (left right : List Bool) :
    polynomialWordAdd left right=rippleTrace (left.length+right.length+1) false left right := by
  exact polynomial_word_add_trace left right

theorem verified_polynomial_word_add_value (left right : List Bool) :
    wordValue (polynomialWordAdd left right)=wordValue left+wordValue right := by
  exact polynomial_word_add_value left right

theorem verified_polynomial_word_add_length (left right : List Bool) :
    (polynomialWordAdd left right).length=left.length+right.length+1 := by
  exact polynomial_word_add_length left right

theorem verified_xor_flag_cobham {n : ℕ} {left right : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) :
    Cobham fun v => xorFlag (left v) (right v) := by
  exact xor_flag_cobham hl hr

theorem verified_adder_pack_cobham {n : ℕ}
    {left right carry output : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) (hc : Cobham carry) (ho : Cobham output) :
    Cobham fun v => adderPack (left v) (right v) (carry v) (output v) := by
  exact adder_pack_cobham hl hr hc ho

theorem verified_word_adder_step_cobham : Cobham fun v : Fin 1 → List Bool => wordAdderStep (v 0) := by
  exact word_adder_step_cobham

theorem verified_word_adder_state_cobham :
    Cobham fun v : Fin 2 → List Bool =>
      (wordAdderStep^[(v 0).length+(v 1).length+1]) (adderPack (v 0) (v 1) [false] []) := by
  exact word_adder_state_cobham

theorem verified_polynomial_word_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordAdd (v 0) (v 1) := by
  exact polynomial_word_add_cobham

theorem verified_encoded_word_add_mem_fp : encodedPolynomialWordAdd ∈ FP := by
  exact encoded_word_add_mem_fp

theorem verified_encoded_word_add_actual_polytime : encodedPolynomialWordAdd ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordAdd (Complexity.pair left right))=
      wordValue left+wordValue right := by
  exact encoded_word_add_actual_polytime

theorem verified_polynomial_word_multiply_value (left right : List Bool) :
    wordValue (polynomialWordMultiply left right)=wordValue left*wordValue right := by
  exact polynomial_word_multiply_value left right

theorem verified_polynomial_word_multiply_length (left right : List Bool) :
    (polynomialWordMultiply left right).length ≤ left.length*(right.length+2) := by
  exact polynomial_word_multiply_length left right

theorem verified_polynomial_word_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordMultiply (v 0) (v 1) := by
  exact polynomial_word_multiply_cobham

theorem verified_encoded_word_multiply_mem_fp : encodedPolynomialWordMultiply ∈ FP := by
  exact encoded_word_multiply_mem_fp

theorem verified_encoded_word_multiply_actual_polytime : encodedPolynomialWordMultiply ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordMultiply (Complexity.pair left right))=
      wordValue left*wordValue right := by
  exact encoded_word_multiply_actual_polytime

#print axioms IV04.Paper.Computational.verified_head_flag
#print axioms IV04.Paper.Computational.verified_wordAdderStep_pack
#print axioms IV04.Paper.Computational.verified_wordAdder_iterate_run
#print axioms IV04.Paper.Computational.verified_adderRun_output
#print axioms IV04.Paper.Computational.verified_adderRun_length
#print axioms IV04.Paper.Computational.verified_ripple_trace_length
#print axioms IV04.Paper.Computational.verified_ripple_trace_zero
#print axioms IV04.Paper.Computational.verified_word_value_head_tail
#print axioms IV04.Paper.Computational.verified_ripple_trace_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_add_trace
#print axioms IV04.Paper.Computational.verified_polynomial_word_add_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_add_length
#print axioms IV04.Paper.Computational.verified_xor_flag_cobham
#print axioms IV04.Paper.Computational.verified_adder_pack_cobham
#print axioms IV04.Paper.Computational.verified_word_adder_step_cobham
#print axioms IV04.Paper.Computational.verified_word_adder_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_word_add_cobham
#print axioms IV04.Paper.Computational.verified_encoded_word_add_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_word_add_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_word_multiply_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_multiply_length
#print axioms IV04.Paper.Computational.verified_polynomial_word_multiply_cobham
#print axioms IV04.Paper.Computational.verified_encoded_word_multiply_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_word_multiply_actual_polytime
end IV04.Paper.Computational
