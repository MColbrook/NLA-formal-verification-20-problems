module

public import NLA.IV04.PaperSATMatrixDefinitions
public import NLA.IV04.PaperPartitionMatrixDecision
public import NLA.IV04.PaperPartitionMatrixPoly
public import NLA.IV04.PaperSATNPCompleteness
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem polynomial_sat_matrix_code_mem_fp : polynomialSATMatrixCode ∈ FP := by
  have hs := FP_subset_CobhamFP polynomial_sat_partition_code_mem_fp
  exact CobhamFP_subset_FP ((Cobham.comp polynomial_partition_matrix_code_cobham
    (fun _ : Fin 1 => hs)).of_eq (fun _ => rfl))

theorem polynomial_sat_partition_output_canonical (input : List Bool) :
    ∃ P : IV04.Paper.IntegerPartition, polynomialSATPartitionCode input=P.inputCode := by
  rw [polynomial_sat_partition_code_exact]
  cases hd : SAT.CNF.decode? input with
  | none =>
    refine ⟨fixedNoPartition,?_⟩
    simp [binarySATPartitionReduction,hd,fixedNoPartition,
      IV04.Paper.IntegerPartition.inputCode,IV04.Paper.IntegerPartition.weightList,countedWeightCode]
  | some formula =>
    exact ⟨actualSATPartition formula,by
      simp only [binarySATPartitionReduction,hd,actual_sat_partition_code]⟩

theorem actual_binary_sat_matrix_reduction (input : List Bool) :
    input ∈ SAT.language ↔ polynomialSATMatrixCode input ∈ rationalMatrixDeterminantDecisionLanguage := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  rw [polynomialSATMatrixCode,hP,polynomial_partition_matrix_language_iff,
    ← paper_partition_code_mem_language P,← hP]
  exact sat_partition_code_actual_polytime.2.2 input

theorem actual_binary_sat_matrix_map_reduction :
    SAT.language ≤ₚ rationalMatrixDeterminantDecisionLanguage :=
  ⟨polynomialSATMatrixCode,polynomial_sat_matrix_code_mem_fp,actual_binary_sat_matrix_reduction⟩

theorem actual_rational_interval_determinant_np_complete :
    NPComplete rationalMatrixDeterminantDecisionLanguage :=
  ⟨rational_matrix_determinant_decision_language_mem_np,
    actual_binary_sat_np_complete.2.of_reduction actual_binary_sat_matrix_map_reduction⟩

theorem actual_sat_matrix_regular_unit_superdiagonal (input : List Bool) :
    ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
      readMatrixRationals (polynomialSATMatrixCode input)=
        some (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]) ∧
      pairs.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
      rationalDenseEndpointAll n 0 0 pairs ∧
      (∀ A ∈ realDenseIntervalBox n pairs, 0 < A.det ∧
        ∀ i j : Fin n, j.val=i.val+1 → A i j=1) := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  have hread := polynomial_partition_matrix_code_read P []
  simp only [List.append_nil] at hread
  refine ⟨P.layerCount,partitionMatrixEndpointPairs P,P.threshold,?_,
    partition_endpoint_pairs_length P,partition_endpoint_pairs_ordered P,
    partition_endpoint_pairs_support P,?_⟩
  · simpa only [polynomialSATMatrixCode,hP] using hread
  · intro A hA
    rw [partition_real_dense_box_exact] at hA
    exact ⟨P.intervalBox_regular A hA,P.intervalBox_superdiagonal A hA⟩

#print axioms polynomial_sat_matrix_code_mem_fp
#print axioms polynomial_sat_partition_output_canonical
#print axioms actual_binary_sat_matrix_reduction
#print axioms actual_binary_sat_matrix_map_reduction
#print axioms actual_rational_interval_determinant_np_complete
#print axioms actual_sat_matrix_regular_unit_superdiagonal
end IV04.Paper.Computational
