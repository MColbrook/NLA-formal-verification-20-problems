module

public import NLA.IV04.PaperStrictMatrixValidation
public import NLA.IV04.PaperTridiagonalCell
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_strict_matrix_selection_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => strictMatrixSelectionFlag (v 0) := by
  exact strict_matrix_selection_flag_cobham

theorem verified_strict_matrix_selection_flag_mem_fp : strictMatrixSelectionFlag ∈ FP := by
  exact strict_matrix_selection_flag_mem_fp

theorem verified_encoded_strict_matrix_selection_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedStrictMatrixSelectionFlag (v 0) := by
  exact encoded_strict_matrix_selection_flag_cobham

theorem verified_encoded_strict_matrix_selection_flag_mem_fp : encodedStrictMatrixSelectionFlag ∈ FP := by
  exact encoded_strict_matrix_selection_flag_mem_fp

theorem verified_strict_matrix_selection_flag_code (b : Bool)
    (dimension denominator words threshold fieldsTail choices tail : List Bool) :
    strictMatrixSelectionFlag
      (pair [b] (pair dimension (pair denominator
        (pair (pair words (pair (pair threshold fieldsTail) choices)) tail))))=
      [decide (b=true ∧ tail=[] ∧ choices=[] ∧ fieldsTail=[])] := by
  exact strict_matrix_selection_flag_code b dimension denominator words threshold fieldsTail choices tail

theorem verified_strict_matrix_selection_flag_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    encodedStrictMatrixSelectionFlag (pair matrix choices)=[false] := by
  exact strict_matrix_selection_flag_decode_failure matrix choices h

theorem verified_strict_matrix_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : n*n ≤ choices.length) :
    encodedStrictMatrixSelectionFlag (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n)] := by
  exact strict_matrix_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices

theorem verified_signed_zero_flag_value (word : List Bool) :
    signedZeroFlag word=[decide (signedWordValue word=0)] := by
  exact signed_zero_flag_value word

theorem verified_tridiagonal_band_flag_value (row column : List Bool) :
    tridiagonalBandFlag row column=
      [decide (wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1)] := by
  exact tridiagonal_band_flag_value row column

theorem verified_tridiagonal_endpoint_flag_value (row column lower upper : List Bool) :
    tridiagonalEndpointFlag row column lower upper=
      [decide ((wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1) ∨
        (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  exact tridiagonal_endpoint_flag_value row column lower upper

theorem verified_signed_zero_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => signedZeroFlag (v 0) := by
  exact signed_zero_flag_cobham

theorem verified_tridiagonal_band_flag_cobham :
    Cobham fun v : Fin 2 → List Bool => tridiagonalBandFlag (v 0) (v 1) := by
  exact tridiagonal_band_flag_cobham

theorem verified_tridiagonal_endpoint_flag_cobham :
    Cobham fun v : Fin 4 → List Bool => tridiagonalEndpointFlag (v 0) (v 1) (v 2) (v 3) := by
  exact tridiagonal_endpoint_flag_cobham

theorem verified_encoded_tridiagonal_endpoint_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedTridiagonalEndpointFlag (v 0) := by
  exact encoded_tridiagonal_endpoint_flag_cobham

theorem verified_encoded_tridiagonal_endpoint_flag_mem_fp : encodedTridiagonalEndpointFlag ∈ FP := by
  exact encoded_tridiagonal_endpoint_flag_mem_fp

theorem verified_encoded_tridiagonal_endpoint_flag_value (row column lower upper : List Bool) :
    encodedTridiagonalEndpointFlag (pair row (pair column (pair lower upper)))=
      [decide ((wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1) ∨
        (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  exact encoded_tridiagonal_endpoint_flag_value row column lower upper

theorem verified_tridiagonal_endpoint_offband (row column lower upper : List Bool)
    (hoff : ¬ (wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1)) :
    encodedTridiagonalEndpointFlag (pair row (pair column (pair lower upper)))=[true] ↔
      signedWordValue lower=0 ∧ signedWordValue upper=0 := by
  exact tridiagonal_endpoint_offband row column lower upper hoff

#print axioms IV04.Paper.Computational.verified_strict_matrix_selection_flag_cobham
#print axioms IV04.Paper.Computational.verified_strict_matrix_selection_flag_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_strict_matrix_selection_flag_cobham
#print axioms IV04.Paper.Computational.verified_encoded_strict_matrix_selection_flag_mem_fp
#print axioms IV04.Paper.Computational.verified_strict_matrix_selection_flag_code
#print axioms IV04.Paper.Computational.verified_strict_matrix_selection_flag_decode_failure
#print axioms IV04.Paper.Computational.verified_strict_matrix_selection_rational_input
#print axioms IV04.Paper.Computational.verified_signed_zero_flag_value
#print axioms IV04.Paper.Computational.verified_tridiagonal_band_flag_value
#print axioms IV04.Paper.Computational.verified_tridiagonal_endpoint_flag_value
#print axioms IV04.Paper.Computational.verified_signed_zero_flag_cobham
#print axioms IV04.Paper.Computational.verified_tridiagonal_band_flag_cobham
#print axioms IV04.Paper.Computational.verified_tridiagonal_endpoint_flag_cobham
#print axioms IV04.Paper.Computational.verified_encoded_tridiagonal_endpoint_flag_cobham
#print axioms IV04.Paper.Computational.verified_encoded_tridiagonal_endpoint_flag_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_tridiagonal_endpoint_flag_value
#print axioms IV04.Paper.Computational.verified_tridiagonal_endpoint_offband
end IV04.Paper.Computational
