module

public import NLA.IV04.PaperBudgetedPowerPoly
public import NLA.IV04.PaperMatrixCoefficientInputBudget
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem budgeted_power_word_bits (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

theorem budgeted_power_decrement_bits (n : ℕ) : decrementCount n.bits=(n-1).bits := by
  rw [decrementCount,canonical_word_eq_bits,polynomial_word_sub_value,budgeted_power_word_bits]
  rfl

theorem budgeted_power_iterate_zero (k : ℕ) (base product : List Bool) :
    (budgetedPowerStep^[k]) (pair [] (pair base product))=pair [] (pair base product) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,budgeted_power_step_pair]; simp

theorem budgeted_power_iterate_value (k n : ℕ) (base product : List Bool) (h : n ≤ k) :
    wordValue (pairSnd (pairSnd ((budgetedPowerStep^[k]) (pair n.bits (pair base product)))))=
      wordValue product * wordValue base ^ n := by
  induction k generalizing n product with
  | zero =>
    have hn : n=0 := by omega
    subst n
    simp [pairSnd_pair]
  | succ k ih =>
    cases n with
    | zero =>
      change wordValue (pairSnd (pairSnd ((budgetedPowerStep^[k+1])
        (pair [] (pair base product)))))=wordValue product * wordValue base ^ 0
      rw [budgeted_power_iterate_zero]
      simp only [pairSnd_pair,pow_zero,Nat.mul_one]
    | succ n =>
      have hc : (n+1).bits ≠ [] := by
        intro he
        have hv := congrArg wordValue he
        rw [budgeted_power_word_bits] at hv
        change n+1=0 at hv
        omega
      rw [Function.iterate_succ_apply,budgeted_power_step_pair]
      simp only [hc,if_false,budgeted_power_decrement_bits,Nat.add_sub_cancel]
      rw [ih n (canonicalWordMultiply product base) (by omega),canonical_word_multiply_value,pow_succ]
      ring

theorem polynomial_budgeted_power_value (input : List Bool)
    (h : wordValue (pairFst input) ≤ input.length) :
    wordValue (polynomialBudgetedPower input)=
      wordValue (pairFst (pairSnd input)) ^ wordValue (pairFst input) := by
  have hv := budgeted_power_iterate_value input.length (wordValue (pairFst input))
    (pairFst (pairSnd input)) [true] h
  simpa only [polynomialBudgetedPower,budgetedPowerState,canonical_word_eq_bits,
    wordValue,bitValue,ite_true,Nat.mul_zero,Nat.zero_add,Nat.one_mul] using hv

theorem polynomial_budgeted_power_code (n : ℕ) (base padding : List Bool)
    (h : n ≤ (pair n.bits (pair base padding)).length) :
    wordValue (polynomialBudgetedPower (pair n.bits (pair base padding)))=wordValue base ^ n := by
  have hb : wordValue (pairFst (pair n.bits (pair base padding))) ≤
      (pair n.bits (pair base padding)).length := by
    simpa only [pairFst_pair,budgeted_power_word_bits] using h
  simpa only [pairFst_pair,pairSnd_pair,budgeted_power_word_bits] using
    polynomial_budgeted_power_value (pair n.bits (pair base padding)) hb

theorem polynomial_budgeted_power_length (input : List Bool) :
    (polynomialBudgetedPower input).length ≤ 4*input.length+5+input.length*input.length := by
  exact ((pairSnd_length_le _).trans (pairSnd_length_le _)).trans (budgeted_power_state_length input)

theorem polynomial_budgeted_power_actual_polytime : polynomialBudgetedPower ∈ FP ∧
    (∀ input, (polynomialBudgetedPower input).length ≤ 4*input.length+5+input.length*input.length) ∧
    (∀ input, wordValue (pairFst input) ≤ input.length →
      wordValue (polynomialBudgetedPower input)=
        wordValue (pairFst (pairSnd input)) ^ wordValue (pairFst input)) :=
  ⟨polynomial_budgeted_power_mem_fp,polynomial_budgeted_power_length,polynomial_budgeted_power_value⟩

theorem matrix_denominator_power_argument_code (input dimension denominator tail : List Bool)
    (coefficients : List (List Bool))
    (h : encodedMatrixCoefficientInput input=
      pair [true] (pair dimension (pair denominator (pair (payloadListCode coefficients) tail)))) :
    matrixDenominatorPowerArgument input=pair dimension (pair denominator input) := by
  simp only [matrixDenominatorPowerArgument,h,pairFst_pair,pairSnd_pair]

theorem matrix_power_count_input_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : n ≤ input.length := by
  have hb := matrix_vertex_certificate_bit_budget input n values tail h
  have hn : n ≤ n*n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_mul,Nat.mul_succ]; omega
  exact hn.trans hb

theorem matrix_denominator_power_successful_input (input : List Bool) (n : ℕ)
    (values : List ℚ) (tail : List Bool) (h : readMatrixRationals input=some (n,values,tail)) :
    wordValue (encodedMatrixDenominatorPower input)=
      wordValue (pairFst (pairSnd (pairSnd (encodedMatrixCoefficientInput input)))) ^ n ∧
      0 < wordValue (encodedMatrixDenominatorPower input) := by
  obtain ⟨dimension,denominator,coefficients,he,hd,hD,_⟩ :=
    matrix_coefficient_input_correct input n values tail h
  have ha := matrix_denominator_power_argument_code input dimension denominator tail coefficients he
  have hn := matrix_power_count_input_budget input n values tail h
  have hc : wordValue (pairFst (pair dimension (pair denominator input))) ≤
      (pair dimension (pair denominator input)).length := by
    simp only [pairFst_pair,pair_length,hd]
    omega
  have hp := polynomial_budgeted_power_value (pair dimension (pair denominator input)) hc
  simp only [pairFst_pair,pairSnd_pair,hd] at hp
  simp only [encodedMatrixDenominatorPower,ha,he,pairFst_pair,pairSnd_pair]
  exact ⟨hp,by rw [hp]; exact pow_pos hD n⟩

#print axioms polynomial_budgeted_power_actual_polytime
#print axioms matrix_denominator_power_successful_input
end IV04.Paper.Computational
