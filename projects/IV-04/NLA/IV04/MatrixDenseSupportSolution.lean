module

public import NLA.IV04.PaperMatrixDenseSupportRational
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_matrix_dense_support_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDenseSupportArgument (v 0) := by
  exact matrix_dense_support_argument_cobham

theorem verified_encoded_matrix_dense_support_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixDenseSupportFlag (v 0) := by
  exact encoded_matrix_dense_support_flag_cobham

theorem verified_encoded_matrix_dense_support_flag_mem_fp : encodedMatrixDenseSupportFlag ∈ FP := by
  exact encoded_matrix_dense_support_flag_mem_fp

theorem verified_matrix_dense_support_argument_code (n : ℕ) (b : Bool) (dimension denominator tail : List Bool)
    (rows : List (List Bool × List Bool)) (rest : List Bool) (hn : wordValue dimension=n) :
    matrixDenseSupportArgument (pair [b] (pair dimension (pair denominator
      (pair (endpointWordPairsCode rows rest) tail))))=denseSupportInputCode n rows rest := by
  exact matrix_dense_support_argument_code n b dimension denominator tail rows rest hn

theorem verified_encoded_matrix_dense_support_flag_code (input : List Bool) (n : ℕ) (b : Bool)
    (dimension denominator tail : List Bool) (rows : List (List Bool × List Bool)) (rest : List Bool)
    (he : encodedMatrixCoefficientInput input=pair [b] (pair dimension (pair denominator
      (pair (endpointWordPairsCode rows rest) tail)))) (hn : wordValue dimension=n) (hsize : rows.length=n*n) :
    encodedMatrixDenseSupportFlag input=[b && decide (denseEndpointAll n 0 0 rows)] := by
  exact encoded_matrix_dense_support_flag_code input n b dimension denominator tail rows rest he hn hsize

theorem verified_encoded_matrix_dense_support_decode_failure (input : List Bool)
    (h : readMatrixRationals input=none) : encodedMatrixDenseSupportFlag input=[false] := by
  exact encoded_matrix_dense_support_decode_failure input h

theorem verified_dense_endpoint_all_scaled (n i j D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (hD : 0 < D)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    denseEndpointAll n i j rows ↔ rationalDenseEndpointAll n i j pairs := by
  exact dense_endpoint_all_scaled n i j D rows pairs hD hrows

theorem verified_matrix_dense_support_rational_input (matrix tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    encodedMatrixDenseSupportFlag matrix=[decide (rationalDenseEndpointAll n 0 0 pairs)] := by
  exact matrix_dense_support_rational_input matrix tail n pairs threshold hread hsize

#print axioms IV04.Paper.Computational.verified_matrix_dense_support_argument_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_dense_support_flag_cobham
#print axioms IV04.Paper.Computational.verified_encoded_matrix_dense_support_flag_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_dense_support_argument_code
#print axioms IV04.Paper.Computational.verified_encoded_matrix_dense_support_flag_code
#print axioms IV04.Paper.Computational.verified_encoded_matrix_dense_support_decode_failure
#print axioms IV04.Paper.Computational.verified_dense_endpoint_all_scaled
#print axioms IV04.Paper.Computational.verified_matrix_dense_support_rational_input
end IV04.Paper.Computational
