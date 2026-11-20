module

public import NLA.IV04.PaperMatrixDenseSupportDefinitions
public import NLA.IV04.PaperDenseTridiagonalSemantics
public import NLA.IV04.PaperMatrixCoefficientInputSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem matrix_dense_support_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDenseSupportArgument (v 0) := by
  have hd := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn
    (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))))
  exact (Cobham.comp₂ Cobham.pairing hd hf).of_eq fun _ => rfl

theorem encoded_matrix_dense_support_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixDenseSupportFlag (v 0) := by
  have hd := encoded_matrix_coefficient_input_cobham
  have ha := Cobham.comp matrix_dense_support_argument_cobham fun _ : Fin 1 => hd
  have hs := Cobham.comp encoded_dense_tridiagonal_support_cobham fun _ : Fin 1 => ha
  exact (Cobham.andFn (Cobham.fstBlockFn hd) (Cobham.fstBlockFn hs)).of_eq fun _ => rfl

theorem encoded_matrix_dense_support_flag_mem_fp : encodedMatrixDenseSupportFlag ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_dense_support_flag_cobham

theorem matrix_dense_support_argument_code (n : ℕ) (b : Bool) (dimension denominator tail : List Bool)
    (rows : List (List Bool × List Bool)) (rest : List Bool) (hn : wordValue dimension=n) :
    matrixDenseSupportArgument (pair [b] (pair dimension (pair denominator
      (pair (endpointWordPairsCode rows rest) tail))))=denseSupportInputCode n rows rest := by
  simp only [matrixDenseSupportArgument,pairFst_pair,pairSnd_pair,canonical_word_eq_bits,hn,denseSupportInputCode]

theorem encoded_matrix_dense_support_flag_code (input : List Bool) (n : ℕ) (b : Bool)
    (dimension denominator tail : List Bool) (rows : List (List Bool × List Bool)) (rest : List Bool)
    (he : encodedMatrixCoefficientInput input=pair [b] (pair dimension (pair denominator
      (pair (endpointWordPairsCode rows rest) tail)))) (hn : wordValue dimension=n) (hsize : rows.length=n*n) :
    encodedMatrixDenseSupportFlag input=[b && decide (denseEndpointAll n 0 0 rows)] := by
  rw [encodedMatrixDenseSupportFlag,he,matrix_dense_support_argument_code n b dimension denominator tail rows rest hn,
    dense_support_input_codes n rows rest hsize,pairFst_pair,pairFst_pair]
  generalize decide (denseEndpointAll n 0 0 rows)=flag
  cases b <;> cases flag <;> rfl

theorem encoded_matrix_dense_support_decode_failure (input : List Bool)
    (h : readMatrixRationals input=none) : encodedMatrixDenseSupportFlag input=[false] := by
  simp [encodedMatrixDenseSupportFlag,matrix_coefficient_input_failure input h,andBit,caseBit₀]

#print axioms encoded_matrix_dense_support_flag_mem_fp
#print axioms encoded_matrix_dense_support_flag_code
#print axioms encoded_matrix_dense_support_decode_failure
end IV04.Paper.Computational
