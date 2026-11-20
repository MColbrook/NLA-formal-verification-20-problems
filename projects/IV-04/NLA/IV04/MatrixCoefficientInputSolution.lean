module

public import NLA.IV04.PaperMatrixCoefficientInputPaper
public import NLA.IV04.PaperMatrixCoefficientInputBudget
public import NLA.IV04.PaperMatrixCoefficientInputBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_matrix_field_count_word_value (dimension : List Bool) :
    wordValue (matrixFieldCountWord dimension)=2*wordValue dimension*wordValue dimension+1 := by
  exact matrix_field_count_word_value dimension

theorem verified_matrix_field_count_word_length (dimension : List Bool) :
    (matrixFieldCountWord dimension).length ≤ 2*dimension.length+3 := by
  exact matrix_field_count_word_length dimension

theorem verified_matrix_field_count_word_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixFieldCountWord (v 0) := by
  exact matrix_field_count_word_cobham

theorem verified_matrix_field_count_word_mem_fp : matrixFieldCountWord ∈ FP := by
  exact matrix_field_count_word_mem_fp

theorem verified_matrix_dimension_word_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDimensionWord (v 0) := by
  exact matrix_dimension_word_cobham

theorem verified_unary_input_cobham_comp {n : ℕ} {f : List Bool → List Bool}
    {g : (Fin n → List Bool) → List Bool}
    (hf : Cobham fun v : Fin 1 → List Bool => f (v 0)) (hg : Cobham g) :
    Cobham fun v => f (g v) := by
  exact unary_input_cobham_comp hf hg

theorem verified_input_pair_cobham_comp {n : ℕ} {left right : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) : Cobham fun v => pair (left v) (right v) := by
  exact input_pair_cobham_comp hl hr

theorem verified_matrix_rational_field_input_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixRationalFieldInput (v 0) := by
  exact matrix_rational_field_input_cobham

theorem verified_encoded_matrix_coefficient_input_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixCoefficientInput (v 0) := by
  exact encoded_matrix_coefficient_input_cobham

theorem verified_encoded_matrix_coefficient_input_mem_fp : encodedMatrixCoefficientInput ∈ FP := by
  exact encoded_matrix_coefficient_input_mem_fp

theorem verified_matrix_dimension_word_length (input : List Bool) :
    (matrixDimensionWord input).length ≤ input.length := by
  exact matrix_dimension_word_length input

theorem verified_matrix_rational_field_input_length (input : List Bool) :
    (matrixRationalFieldInput input).length ≤ 4*input.length+8 := by
  exact matrix_rational_field_input_length input

theorem verified_natural_parser_success_shape (input : List Bool) (n : ℕ) (tail : List Bool)
    (h : IV04.Paper.readNatural input=some (n,tail)) :
    ∃ payload, encodedNaturalParser input=pair [true] (pair payload tail) ∧ wordValue payload=n := by
  exact natural_parser_success_shape input n tail h

theorem verified_natural_parser_failure_flag (input : List Bool) (h : IV04.Paper.readNatural input=none) :
    pairFst (encodedNaturalParser input)=[false] := by
  exact natural_parser_failure_flag input h

theorem verified_read_rationals_result_length (count : ℕ) (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals count input=some (values,tail)) : values.length=count := by
  exact read_rationals_result_length count input values tail h

theorem verified_matrix_rational_field_input_count (input : List Bool) :
    wordValue (pairFst (matrixRationalFieldInput input))=
      2*wordValue (pairFst (pairSnd (encodedNaturalParser input)))*
        wordValue (pairFst (pairSnd (encodedNaturalParser input)))+1 := by
  exact matrix_rational_field_input_count input

theorem verified_matrix_rational_field_input_tail (input : List Bool) :
    pairSnd (matrixRationalFieldInput input)=pairSnd (pairSnd (encodedNaturalParser input)) := by
  exact matrix_rational_field_input_tail input

theorem verified_matrix_coefficient_input_correct (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput input=pair [true]
        (pair dimension (pair denominator (pair (payloadListCode coefficients) tail))) ∧
      wordValue dimension=n ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*n*n+1 := by
  exact matrix_coefficient_input_correct input n values tail h

theorem verified_matrix_coefficient_input_failure (input : List Bool) (h : readMatrixRationals input=none) :
    pairFst (encodedMatrixCoefficientInput input)=[false] := by
  exact matrix_coefficient_input_failure input h

theorem verified_matrix_coefficient_input_valid_iff (input : List Bool) :
    pairFst (encodedMatrixCoefficientInput input)=[true] ↔
      ∃ n values tail, readMatrixRationals input=some (n,values,tail) := by
  exact matrix_coefficient_input_valid_iff input

theorem verified_read_matrix_rationals_codes (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : values.length=2*n*n+1) :
    readMatrixRationals (IV04.Paper.naturalCode n ++ (values.flatMap IV04.Paper.rationalCode ++ tail))=
      some (n,values,tail) := by
  exact read_matrix_rationals_codes n values tail h

theorem verified_matrix_coefficient_input_actual_polytime : encodedMatrixCoefficientInput ∈ FP ∧
    ∀ input n values tail, readMatrixRationals input=some (n,values,tail) →
      ∃ dimension denominator coefficients,
        encodedMatrixCoefficientInput input=pair [true]
          (pair dimension (pair denominator (pair (payloadListCode coefficients) tail))) ∧
        wordValue dimension=n ∧ 0 < wordValue denominator ∧
        coefficients.map (fun w => (signedWordValue w : ℚ))=
          values.map (fun q => q*(wordValue denominator : ℚ)) ∧
        coefficients.length=2*n*n+1 := by
  exact matrix_coefficient_input_actual_polytime

theorem verified_read_rational_result_budget (input : List Bool) (q : ℚ) (tail : List Bool)
    (h : IV04.Paper.readRational input=some (q,tail)) : tail.length+3 ≤ input.length := by
  exact read_rational_result_budget input q tail h

theorem verified_read_rationals_input_budget (count : ℕ) (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals count input=some (values,tail)) : tail.length+3*count ≤ input.length := by
  exact read_rationals_input_budget count input values tail h

theorem verified_read_matrix_dimension_input_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : tail.length+6*n*n+4 ≤ input.length := by
  exact read_matrix_dimension_input_budget input n values tail h

theorem verified_matrix_vertex_certificate_bit_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : n*n ≤ input.length := by
  exact matrix_vertex_certificate_bit_budget input n values tail h

theorem verified_flat_map_constant_length {α β : Type} (values : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ values, (f x).length=k) : (values.flatMap f).length=values.length*k := by
  exact flat_map_constant_length values f k h

theorem verified_dense_endpoint_rationals_length {n : ℕ} (lower upper : RatMat n) :
    (denseEndpointRationals lower upper).length=2*n*n := by
  exact dense_endpoint_rationals_length lower upper

theorem verified_matrix_endpoint_rationals_length {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) :
    (matrixEndpointRationals lower upper threshold).length=2*n*n+1 := by
  exact matrix_endpoint_rationals_length lower upper threshold

theorem verified_read_dense_matrix_threshold_code {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) (tail : List Bool) :
    readMatrixRationals (denseMatrixThresholdCode lower upper threshold ++ tail)=
      some (n,matrixEndpointRationals lower upper threshold,tail) := by
  exact read_dense_matrix_threshold_code lower upper threshold tail

theorem verified_matrix_coefficient_input_dense_codes {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) (tail : List Bool) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput (denseMatrixThresholdCode lower upper threshold ++ tail)=
        Complexity.pair [true] (Complexity.pair dimension
          (Complexity.pair denominator (Complexity.pair (payloadListCode coefficients) tail))) ∧
      wordValue dimension=n ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        (matrixEndpointRationals lower upper threshold).map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*n*n+1 := by
  exact matrix_coefficient_input_dense_codes lower upper threshold tail

theorem verified_paper_matrix_box_code_eq (P : IV04.Paper.IntegerPartition) :
    P.matrixBoxCode=denseMatrixThresholdCode P.rationalLower P.rationalUpper P.threshold := by
  exact paper_matrix_box_code_eq P

theorem verified_matrix_coefficient_input_paper_box (P : IV04.Paper.IntegerPartition) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput P.matrixBoxCode=
        Complexity.pair [true] (Complexity.pair dimension
          (Complexity.pair denominator (Complexity.pair (payloadListCode coefficients) []))) ∧
      wordValue dimension=P.layerCount ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        (matrixEndpointRationals P.rationalLower P.rationalUpper P.threshold).map
          (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*P.layerCount*P.layerCount+1 := by
  exact matrix_coefficient_input_paper_box P

#print axioms IV04.Paper.Computational.verified_matrix_field_count_word_value
#print axioms IV04.Paper.Computational.verified_matrix_field_count_word_length
#print axioms IV04.Paper.Computational.verified_matrix_field_count_word_cobham
#print axioms IV04.Paper.Computational.verified_matrix_field_count_word_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_dimension_word_cobham
#print axioms IV04.Paper.Computational.verified_unary_input_cobham_comp
#print axioms IV04.Paper.Computational.verified_input_pair_cobham_comp
#print axioms IV04.Paper.Computational.verified_matrix_rational_field_input_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_coefficient_input_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_coefficient_input_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_dimension_word_length
#print axioms IV04.Paper.Computational.verified_matrix_rational_field_input_length
#print axioms IV04.Paper.Computational.verified_natural_parser_success_shape
#print axioms IV04.Paper.Computational.verified_natural_parser_failure_flag
#print axioms IV04.Paper.Computational.verified_read_rationals_result_length
#print axioms IV04.Paper.Computational.verified_matrix_rational_field_input_count
#print axioms IV04.Paper.Computational.verified_matrix_rational_field_input_tail
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_correct
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_failure
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_valid_iff
#print axioms IV04.Paper.Computational.verified_read_matrix_rationals_codes
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_actual_polytime
#print axioms IV04.Paper.Computational.verified_read_rational_result_budget
#print axioms IV04.Paper.Computational.verified_read_rationals_input_budget
#print axioms IV04.Paper.Computational.verified_read_matrix_dimension_input_budget
#print axioms IV04.Paper.Computational.verified_matrix_vertex_certificate_bit_budget
#print axioms IV04.Paper.Computational.verified_flat_map_constant_length
#print axioms IV04.Paper.Computational.verified_dense_endpoint_rationals_length
#print axioms IV04.Paper.Computational.verified_matrix_endpoint_rationals_length
#print axioms IV04.Paper.Computational.verified_read_dense_matrix_threshold_code
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_dense_codes
#print axioms IV04.Paper.Computational.verified_paper_matrix_box_code_eq
#print axioms IV04.Paper.Computational.verified_matrix_coefficient_input_paper_box
end IV04.Paper.Computational
