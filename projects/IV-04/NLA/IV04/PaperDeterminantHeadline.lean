module

public import NLA.IV04.PaperDeterminantHeadlineDefinitions
public import NLA.IV04.PaperExactOutputHardness
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem actual_sat_matrix_packet_regular :
  ∀ input : List Bool, RegularUnitMatrixPacket (polynomialSATMatrixCode input) := by
  intro input
  obtain ⟨n,pairs,threshold,hr,hlen,horder,hsupport,hreg⟩ :=
    actual_sat_matrix_regular_unit_superdiagonal input
  exact ⟨n,pairs,threshold,hr,hlen,horder,hsupport,
    fun A hA => ⟨ne_of_gt (hreg A hA).1,(hreg A hA).2⟩⟩
#print axioms actual_sat_matrix_packet_regular

theorem actual_sat_output_query_packet_regular :
  ∀ input : List Bool, RegularUnitMatrixPacket (polynomialSATOutputQuery input) := by
  intro input
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  have hread := polynomial_partition_output_query_read P []
  simp only [List.append_nil] at hread
  refine ⟨P.layerCount,partitionMatrixEndpointPairs P,0,?_,
    partition_endpoint_pairs_length P,partition_endpoint_pairs_ordered P,
    partition_endpoint_pairs_support P,?_⟩
  · simpa only [polynomialSATOutputQuery,hP] using hread
  · intro A hA
    rw [partition_real_dense_box_exact] at hA
    exact ⟨ne_of_gt (P.intervalBox_regular A hA),P.intervalBox_superdiagonal A hA⟩
#print axioms actual_sat_output_query_packet_regular

theorem actual_binary_sat_regular_determinant_reduction :
  ∀ input : List Bool, input ∈ SAT.language ↔ polynomialSATMatrixCode input ∈ regularUnitMatrixDeterminantDecisionLanguage := by
  intro input
  constructor
  · intro h
    exact ⟨(actual_binary_sat_matrix_reduction input).mp h,
      actual_sat_matrix_packet_regular input⟩
  · intro h
    exact (actual_binary_sat_matrix_reduction input).mpr h.1
#print axioms actual_binary_sat_regular_determinant_reduction

theorem actual_binary_sat_regular_determinant_map_reduction :
  SAT.language ≤ₚ regularUnitMatrixDeterminantDecisionLanguage := ⟨polynomialSATMatrixCode,polynomial_sat_matrix_code_mem_fp,
    actual_binary_sat_regular_determinant_reduction⟩
#print axioms actual_binary_sat_regular_determinant_map_reduction

theorem actual_regular_unit_determinant_np_hard :
  NPHard regularUnitMatrixDeterminantDecisionLanguage := actual_binary_sat_np_complete.2.of_reduction
    actual_binary_sat_regular_determinant_map_reduction
#print axioms actual_regular_unit_determinant_np_hard

theorem regular_unit_exact_determinant_range_output_np_hard :
  NPHardOutputTask RegularUnitDeterminantRangeOutput := by
  have hs : PolynomialOneQueryReduction SAT.language RegularUnitDeterminantRangeOutput := by
    refine ⟨polynomialSATOutputQuery,polynomial_sat_output_query_mem_fp,
      polynomialSATRangeAnswer,polynomial_sat_range_answer_mem_fp,?_,?_⟩
    · intro input
      obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
      obtain ⟨answer,ha⟩ := partition_exact_range_output_exists P
      refine ⟨answer,?_,actual_sat_output_query_packet_regular input⟩
      simpa only [polynomialSATOutputQuery,hP] using ha
    · intro input answer h
      exact polynomial_sat_range_answer_correct input answer h.1
  intro L hL
  exact one_query_reduction_of_map (actual_binary_sat_np_complete.2 L hL) hs
#print axioms regular_unit_exact_determinant_range_output_np_hard

theorem actual_paper_iv_det :
  NPComplete rationalMatrixDeterminantDecisionLanguage ∧
  NPHard regularUnitMatrixDeterminantDecisionLanguage ∧
  NPHardOutputTask RegularUnitDeterminantRangeOutput := ⟨actual_rational_interval_determinant_np_complete,
    actual_regular_unit_determinant_np_hard,regular_unit_exact_determinant_range_output_np_hard⟩
#print axioms actual_paper_iv_det
end IV04.Paper.Computational
