module

public import NLA.IV04.PaperPartitionMatrixEndpointSemantics
public import NLA.IV04.PaperBoundedPayloadMapSemantics
public import NLA.IV04.PaperInputEncoding
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem partition_reverse_range_flatMap {α : Type*} (n : ℕ) (f : ℕ → List α) :
    (List.range n).reverse.flatMap (fun k => f (n-1-k)) = (List.range n).flatMap f := by
  have h : (List.range n).reverse = (List.range n).map (fun k => n-1-k) := by
    simpa only [List.range_eq_range',Nat.zero_add] using (List.reverse_range' (s := 0) (n := n))
  have hh : (List.range n).reverse.map (fun k => n-1-k) = List.range n := by
    rw [List.map_reverse,← h,List.reverse_reverse]
  calc
    _ = ((List.range n).reverse.map (fun k => n-1-k)).flatMap f := by
      simp only [List.flatMap_map]
    _ = _ := congrArg (fun xs => xs.flatMap f) hh

theorem partition_ruler_clock (P : IV04.Paper.IntegerPartition) :
    P.layerCount ≤ (polynomialPartitionRuler P.inputCode).length+1 := by
  have hm : P.m ≤ P.inputCode.length := by
    rw [P.input_code_length]
    omega
  simp only [polynomialPartitionRuler,smash,List.length_replicate,List.length_cons,
    List.length_cons,List.length_nil] 
  dsimp [IV04.Paper.IntegerPartition.layerCount]
  omega

theorem polynomial_partition_column_chunk_shape (P : IV04.Paper.IntegerPartition)
    (i k : ℕ) :
    polynomialPartitionColumnChunk (pair (pair P.inputCode i.bits) k.bits) =
      polynomialPartitionEndpointFields (pair P.inputCode (pair i.bits (P.layerCount-1-k).bits)) := by
  simp only [polynomialPartitionColumnChunk,pairFst_pair,pairSnd_pair,
    partition_reverse_index_word,polynomial_partition_layer_count_value,partition_bits_value]

theorem polynomial_partition_row_chunk_shape (P : IV04.Paper.IntegerPartition) (k : ℕ) :
    polynomialPartitionRowChunk (pair P.inputCode k.bits) =
      (List.range P.layerCount).flatMap (fun j => polynomialPartitionEndpointFields
        (pair P.inputCode (pair (P.layerCount-1-k).bits j.bits))) := by
  simp only [polynomialPartitionRowChunk,pairFst_pair,pairSnd_pair,
    partition_reverse_index_word,polynomial_partition_layer_count_value,partition_bits_value,
    partition_layer_count_word]
  rw [polynomial_bounded_payload_map_exact polynomialPartitionColumnChunk
    (polynomialPartitionRuler P.inputCode) (pair P.inputCode (P.layerCount-1-k).bits)
    P.layerCount (partition_ruler_clock P)]
  simp only [polynomial_partition_column_chunk_shape P]
  exact partition_reverse_range_flatMap P.layerCount (fun j => polynomialPartitionEndpointFields
    (pair P.inputCode (pair (P.layerCount-1-k).bits j.bits)))

theorem polynomial_partition_endpoint_table_shape (P : IV04.Paper.IntegerPartition) :
    polynomialPartitionEndpointTable P.inputCode =
      (List.range P.layerCount).flatMap (fun i => (List.range P.layerCount).flatMap
        (fun j => polynomialPartitionEndpointFields (pair P.inputCode (pair i.bits j.bits)))) := by
  simp only [polynomialPartitionEndpointTable,partition_layer_count_word]
  rw [polynomial_bounded_payload_map_exact polynomialPartitionRowChunk
    (polynomialPartitionRuler P.inputCode) P.inputCode P.layerCount (partition_ruler_clock P)]
  have hrow : (fun i : ℕ => polynomialPartitionRowChunk (pair P.inputCode i.bits)) =
      (fun i : ℕ => (List.range P.layerCount).flatMap (fun j =>
        polynomialPartitionEndpointFields (pair P.inputCode (pair (P.layerCount-1-i).bits j.bits)))) := by
    funext i
    exact polynomial_partition_row_chunk_shape P i
  have hmap := congrArg (fun f : ℕ → List Bool => (List.range P.layerCount).reverse.flatMap f) hrow
  with_reducible exact hmap.trans (partition_reverse_range_flatMap P.layerCount (fun i =>
    (List.range P.layerCount).flatMap (fun j => polynomialPartitionEndpointFields
      (pair P.inputCode (pair i.bits j.bits)))))


#print axioms partition_reverse_range_flatMap
#print axioms partition_ruler_clock
#print axioms polynomial_partition_column_chunk_shape
#print axioms polynomial_partition_row_chunk_shape
#print axioms polynomial_partition_endpoint_table_shape
end IV04.Paper.Computational
