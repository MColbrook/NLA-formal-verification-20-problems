module

public import NLA.IV04.PaperPartitionMatrixLayoutSemantics
public import NLA.IV04.PaperPartitionMatrixOutputDefinitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem partition_finrange_values (n : ℕ) :
    (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem partition_matrix_index_pairs_length (P : IV04.Paper.IntegerPartition) :
    (partitionMatrixIndexPairs P).length = P.layerCount*P.layerCount := by
  simp [partitionMatrixIndexPairs,List.length_flatMap]

theorem polynomial_partition_endpoint_table_fin (P : IV04.Paper.IntegerPartition) :
    polynomialPartitionEndpointTable P.inputCode =
      (partitionMatrixIndexPairs P).flatMap (fun ij =>
        polynomialPartitionEndpointFields (pair P.inputCode (pair ij.1.val.bits ij.2.val.bits))) := by
  rw [polynomial_partition_endpoint_table_shape]
  simp only [← partition_finrange_values P.layerCount,partitionMatrixIndexPairs,
    List.flatMap_map,List.flatMap_assoc]

theorem read_rationals_append (a b : ℕ) (input : List Bool) :
    readRationals (a+b) input = (do
      let (xs,rest) ← readRationals a input
      let (ys,tail) ← readRationals b rest
      return (xs++ys,tail)) := by
  induction a generalizing input with
  | zero => simp [readRationals,Option.pure_def]
  | succ a ih =>
    cases hq : IV04.Paper.readRational input with
    | none => simp [Nat.succ_add,readRationals,hq,bind]
    | some qt =>
      rcases qt with ⟨q,rest⟩
      simp only [Nat.succ_add,readRationals,hq,bind,Option.bind_some]
      rw [ih]
      cases hs : readRationals a rest with
      | none => simp [hs]
      | some st =>
        rcases st with ⟨xs,last⟩
        cases ht : readRationals b last <;>
          simp [hs,ht,bind,Option.pure_def]

theorem partition_endpoint_chunks_read (P : IV04.Paper.IntegerPartition)
    (indices : List (Fin P.layerCount × Fin P.layerCount)) (tail : List Bool) :
    readRationals (2*indices.length)
      (indices.flatMap (fun ij => polynomialPartitionEndpointFields
        (pair P.inputCode (pair ij.1.val.bits ij.2.val.bits))) ++ tail) =
      some (indices.flatMap (fun ij => [P.rationalLower ij.1 ij.2,P.rationalUpper ij.1 ij.2]),tail) := by
  induction indices with
  | nil => rfl
  | cons ij indices ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc]
    rw [show 2*(indices.length+1)=2+2*indices.length by omega,read_rationals_append]
    rw [polynomial_partition_endpoint_fields_read]
    simp only [bind,Option.bind_some,ih,Option.pure_def]

theorem polynomial_partition_table_read (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    readRationals (2*P.layerCount*P.layerCount) (polynomialPartitionEndpointTable P.inputCode ++ tail) =
      some ((partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2]),tail) := by
  have h := partition_endpoint_chunks_read P (partitionMatrixIndexPairs P) tail
  simpa only [partition_matrix_index_pairs_length,Nat.mul_assoc,
    ← polynomial_partition_endpoint_table_fin,partitionMatrixEndpointPairs,List.flatMap_map] using h

theorem polynomial_partition_matrix_code_read (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    readMatrixRationals (polynomialPartitionMatrixCode P.inputCode ++ tail) =
      some (P.layerCount,(partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2])++[P.threshold],tail) := by
  simp only [polynomialPartitionMatrixCode,partition_layer_count_word,canonical_word_code_exact,
    partition_bits_value,List.append_assoc,readMatrixRationals,IV04.Paper.read_natural_code,
    bind,Option.bind_some]
  rw [read_rationals_append,polynomial_partition_table_read]
  simp only [bind,Option.bind_some,readRationals,polynomial_fraction_output_read,
    polynomial_partition_threshold_fraction_value,Option.pure_def]

#print axioms partition_finrange_values
#print axioms partition_matrix_index_pairs_length
#print axioms polynomial_partition_endpoint_table_fin
#print axioms read_rationals_append
#print axioms partition_endpoint_chunks_read
#print axioms polynomial_partition_table_read
#print axioms polynomial_partition_matrix_code_read
end IV04.Paper.Computational
