module

public import NLA.IV04.PaperBudgetedPowerSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_budgeted_power_step_pair (count base product : List Bool) :
    budgetedPowerStep (pair count (pair base product))=
      if count=[] then pair count (pair base product) else
        pair (decrementCount count) (pair base (canonicalWordMultiply product base)) := by
  exact budgeted_power_step_pair count base product

theorem verified_budgeted_power_step_shape (count base product : List Bool) :
    ∃ c p : List Bool, budgetedPowerStep (pair count (pair base product))=pair c (pair base p) ∧
      c.length ≤ count.length ∧ p.length ≤ product.length+base.length := by
  exact budgeted_power_step_shape count base product

theorem verified_budgeted_power_iterate_shape (k : ℕ) (count base product : List Bool) :
    ∃ c p : List Bool, (budgetedPowerStep^[k]) (pair count (pair base product))=pair c (pair base p) ∧
      c.length ≤ count.length ∧ p.length ≤ product.length+k*base.length := by
  exact budgeted_power_iterate_shape k count base product

theorem verified_budgeted_power_iterate_length (k : ℕ) (count base product : List Bool) :
    ((budgetedPowerStep^[k]) (pair count (pair base product))).length ≤
      2*count.length+2*base.length+product.length+4+k*base.length := by
  exact budgeted_power_iterate_length k count base product

theorem verified_budgeted_power_clock_length (clock input : List Bool) :
    ((budgetedPowerStep^[clock.length])
      (pair (canonicalWord (pairFst input)) (pair (pairFst (pairSnd input)) [true]))).length ≤
      4*input.length+5+clock.length*input.length := by
  exact budgeted_power_clock_length clock input

theorem verified_budgeted_power_state_length (input : List Bool) :
    (budgetedPowerState input).length ≤ 4*input.length+5+input.length*input.length := by
  exact budgeted_power_state_length input

theorem verified_budgeted_power_step_cobham :
    Cobham fun v : Fin 1 → List Bool => budgetedPowerStep (v 0) := by
  exact budgeted_power_step_cobham

theorem verified_budgeted_power_state_cobham :
    Cobham fun v : Fin 1 → List Bool => budgetedPowerState (v 0) := by
  exact budgeted_power_state_cobham

theorem verified_polynomial_budgeted_power_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialBudgetedPower (v 0) := by
  exact polynomial_budgeted_power_cobham

theorem verified_polynomial_budgeted_power_mem_fp : polynomialBudgetedPower ∈ FP := by
  exact polynomial_budgeted_power_mem_fp

theorem verified_matrix_denominator_power_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDenominatorPowerArgument (v 0) := by
  exact matrix_denominator_power_argument_cobham

theorem verified_encoded_matrix_denominator_power_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixDenominatorPower (v 0) := by
  exact encoded_matrix_denominator_power_cobham

theorem verified_encoded_matrix_denominator_power_mem_fp : encodedMatrixDenominatorPower ∈ FP := by
  exact encoded_matrix_denominator_power_mem_fp

theorem verified_budgeted_power_word_bits (n : ℕ) : wordValue n.bits=n := by
  exact budgeted_power_word_bits n

theorem verified_budgeted_power_decrement_bits (n : ℕ) : decrementCount n.bits=(n-1).bits := by
  exact budgeted_power_decrement_bits n

theorem verified_budgeted_power_iterate_zero (k : ℕ) (base product : List Bool) :
    (budgetedPowerStep^[k]) (pair [] (pair base product))=pair [] (pair base product) := by
  exact budgeted_power_iterate_zero k base product

theorem verified_budgeted_power_iterate_value (k n : ℕ) (base product : List Bool) (h : n ≤ k) :
    wordValue (pairSnd (pairSnd ((budgetedPowerStep^[k]) (pair n.bits (pair base product)))))=
      wordValue product * wordValue base ^ n := by
  exact budgeted_power_iterate_value k n base product h

theorem verified_polynomial_budgeted_power_value (input : List Bool)
    (h : wordValue (pairFst input) ≤ input.length) :
    wordValue (polynomialBudgetedPower input)=
      wordValue (pairFst (pairSnd input)) ^ wordValue (pairFst input) := by
  exact polynomial_budgeted_power_value input h

theorem verified_polynomial_budgeted_power_code (n : ℕ) (base padding : List Bool)
    (h : n ≤ (pair n.bits (pair base padding)).length) :
    wordValue (polynomialBudgetedPower (pair n.bits (pair base padding)))=wordValue base ^ n := by
  exact polynomial_budgeted_power_code n base padding h

theorem verified_polynomial_budgeted_power_length (input : List Bool) :
    (polynomialBudgetedPower input).length ≤ 4*input.length+5+input.length*input.length := by
  exact polynomial_budgeted_power_length input

theorem verified_polynomial_budgeted_power_actual_polytime : polynomialBudgetedPower ∈ FP ∧
    (∀ input, (polynomialBudgetedPower input).length ≤ 4*input.length+5+input.length*input.length) ∧
    (∀ input, wordValue (pairFst input) ≤ input.length →
      wordValue (polynomialBudgetedPower input)=
        wordValue (pairFst (pairSnd input)) ^ wordValue (pairFst input)) := by
  exact polynomial_budgeted_power_actual_polytime

theorem verified_matrix_denominator_power_argument_code (input dimension denominator tail : List Bool)
    (coefficients : List (List Bool))
    (h : encodedMatrixCoefficientInput input=
      pair [true] (pair dimension (pair denominator (pair (payloadListCode coefficients) tail)))) :
    matrixDenominatorPowerArgument input=pair dimension (pair denominator input) := by
  exact matrix_denominator_power_argument_code input dimension denominator tail coefficients h

theorem verified_matrix_power_count_input_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : n ≤ input.length := by
  exact matrix_power_count_input_budget input n values tail h

theorem verified_matrix_denominator_power_successful_input (input : List Bool) (n : ℕ)
    (values : List ℚ) (tail : List Bool) (h : readMatrixRationals input=some (n,values,tail)) :
    wordValue (encodedMatrixDenominatorPower input)=
      wordValue (pairFst (pairSnd (pairSnd (encodedMatrixCoefficientInput input)))) ^ n ∧
      0 < wordValue (encodedMatrixDenominatorPower input) := by
  exact matrix_denominator_power_successful_input input n values tail h

#print axioms IV04.Paper.Computational.verified_budgeted_power_step_pair
#print axioms IV04.Paper.Computational.verified_budgeted_power_step_shape
#print axioms IV04.Paper.Computational.verified_budgeted_power_iterate_shape
#print axioms IV04.Paper.Computational.verified_budgeted_power_iterate_length
#print axioms IV04.Paper.Computational.verified_budgeted_power_clock_length
#print axioms IV04.Paper.Computational.verified_budgeted_power_state_length
#print axioms IV04.Paper.Computational.verified_budgeted_power_step_cobham
#print axioms IV04.Paper.Computational.verified_budgeted_power_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_denominator_power_argument_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_denominator_power_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_denominator_power_mem_fp
#print axioms IV04.Paper.Computational.verified_budgeted_power_word_bits
#print axioms IV04.Paper.Computational.verified_budgeted_power_decrement_bits
#print axioms IV04.Paper.Computational.verified_budgeted_power_iterate_zero
#print axioms IV04.Paper.Computational.verified_budgeted_power_iterate_value
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_value
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_code
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_length
#print axioms IV04.Paper.Computational.verified_polynomial_budgeted_power_actual_polytime
#print axioms IV04.Paper.Computational.verified_matrix_denominator_power_argument_code
#print axioms IV04.Paper.Computational.verified_matrix_power_count_input_budget
#print axioms IV04.Paper.Computational.verified_matrix_denominator_power_successful_input
end IV04.Paper.Computational
