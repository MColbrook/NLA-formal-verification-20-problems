module

public import NLA.IV04.PaperExactOutputHardnessSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem partition_exact_range_output_exists (P : IV04.Paper.IntegerPartition) :
    ∃ answer, ExactDeterminantRangeOutput (polynomialPartitionOutputQuery P.inputCode) answer := by
  obtain ⟨lc,hlc,hmin⟩ := actual_real_interval_determinant_minimum_vertex P.layerCount
    (partitionMatrixEndpointPairs P) (partition_endpoint_pairs_ordered P)
  obtain ⟨uc,huc,hmax⟩ := actual_real_interval_determinant_maximum_vertex P.layerCount
    (partitionMatrixEndpointPairs P) (partition_endpoint_pairs_ordered P)
  let lo := (rationalEndpointVertex P.layerCount (partitionMatrixEndpointPairs P) lc).det
  let hi := (rationalEndpointVertex P.layerCount (partitionMatrixEndpointPairs P) uc).det
  refine ⟨IV04.Paper.rationalCode lo ++ IV04.Paper.rationalCode hi,P.layerCount,
    partitionMatrixEndpointPairs P,?_,partition_endpoint_pairs_length P,
    partition_endpoint_pairs_ordered P,partition_endpoint_pairs_support P,
    lo,hi,IV04.Paper.rationalCode hi,IV04.Paper.read_rational_code lo _,?_,hmin,hmax⟩
  · simpa only [List.append_nil] using polynomial_partition_output_query_read P []
  · simpa only [List.append_nil] using IV04.Paper.read_rational_code hi []

theorem polynomial_sat_range_answer_correct (input answer : List Bool)
    (h : ExactDeterminantRangeOutput (polynomialSATOutputQuery input) answer) :
    firstBit (polynomialSATRangeAnswer (pair input answer)) = true ↔ input ∈ SAT.language := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  unfold polynomialSATOutputQuery at h
  rw [hP] at h
  obtain ⟨n,pairs,hr,hlen,_,_,lo,hi,tail,hl,hh,hmin,hmax⟩ := h
  obtain ⟨hn,hpairs⟩ := polynomial_partition_output_query_identifies P n pairs hr hlen
  subst n
  subst pairs
  rw [partition_real_dense_box_exact] at hmin hmax
  have hsat : input ∈ SAT.language ↔ P.HasPartition := by
    rw [← paper_partition_code_mem_language P,← hP]
    exact sat_partition_code_actual_polytime.2.2 input
  have hthreshold : P.HasPartition ↔ (P.threshold : ℝ) ≤ (hi : ℝ) := by
    constructor
    · intro hp
      obtain ⟨A,hA,hdet⟩ := P.intervalBox_partition_threshold.mp hp
      exact hdet.trans (hmax.2 ⟨A,hA,rfl⟩)
    · intro hp
      obtain ⟨A,hA,hdet⟩ := hmax.1
      exact P.intervalBox_partition_threshold.mpr ⟨A,hA,by rw [hdet];exact hp⟩
  have hiff : P.threshold ≤ hi ↔ input ∈ SAT.language := by
    rw [hsat]
    simpa only [Rat.cast_le] using hthreshold.symm
  have hfirst := rational_parser_success_value_tail answer lo tail hl
  have hsecond := rational_parser_success_value_tail tail hi [] hh
  rw [polynomialSATRangeAnswer,pairFst_pair,pairSnd_pair,hP,hfirst.2,
    polynomial_fraction_le_value,polynomial_partition_threshold_fraction_value,hsecond.1]
  simpa only [firstBit,List.headD_cons,decide_eq_true_eq] using hiff

theorem exact_determinant_range_output_np_hard : NPHardOutputTask ExactDeterminantRangeOutput := by
  have hs : PolynomialOneQueryReduction SAT.language ExactDeterminantRangeOutput := by
    refine ⟨polynomialSATOutputQuery,polynomial_sat_output_query_mem_fp,
      polynomialSATRangeAnswer,polynomial_sat_range_answer_mem_fp,?_,polynomial_sat_range_answer_correct⟩
    intro input
    obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
    simpa only [polynomialSATOutputQuery,hP] using partition_exact_range_output_exists P
  intro L hL
  exact one_query_reduction_of_map (actual_binary_sat_np_complete.2 L hL) hs

theorem partition_exact_first_hull_output_exists (P : IV04.Paper.IntegerPartition) :
    ∃ answer, ExactFirstHullEndpointOutput (polynomialPartitionOutputQuery P.inputCode) answer := by
  obtain ⟨uc,huc,hvertex⟩ := actual_real_interval_determinant_maximum_vertex P.layerCount
    (partitionMatrixEndpointPairs P) (partition_endpoint_pairs_ordered P)
  rw [partition_real_dense_box_exact] at hvertex
  obtain ⟨A,hA,hmax,hmin,hne,hbounded⟩ := P.constructed_hull_endpoint
  let hi := (rationalEndpointVertex P.layerCount (partitionMatrixEndpointPairs P) uc).det
  have heq : A.det = (hi : ℝ) := le_antisymm (hvertex.2 hmax.1) (hmax.2 hvertex.1)
  refine ⟨IV04.Paper.rationalCode (1/hi),P.layerCount,P.layerCount_pos,
    partitionMatrixEndpointPairs P,?_,partition_endpoint_pairs_length P,
    partition_endpoint_pairs_ordered P,partition_endpoint_pairs_support P,?_,?_,?_,
    1/hi,?_,?_⟩
  · simpa only [List.append_nil] using polynomial_partition_output_query_read P []
  · intro B hB
    rw [partition_real_dense_box_exact] at hB
    exact ⟨ne_of_gt (P.intervalBox_regular B hB),P.intervalBox_superdiagonal B hB⟩
  · rw [partition_real_dense_box_exact]
    exact hne
  · rw [partition_real_dense_box_exact]
    exact hbounded
  · simpa only [List.append_nil] using IV04.Paper.read_rational_code (1/hi) []
  · rw [partition_real_dense_box_exact]
    change IsLeast P.constructedFirstCoordinates ((1/hi : ℚ) : ℝ)
    simpa only [Rat.cast_div,Rat.cast_one,heq] using hmin

theorem polynomial_sat_first_hull_answer_correct (input answer : List Bool)
    (h : ExactFirstHullEndpointOutput (polynomialSATOutputQuery input) answer) :
    firstBit (polynomialSATHullAnswer (pair input answer)) = true ↔ input ∈ SAT.language := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  unfold polynomialSATOutputQuery at h
  rw [hP] at h
  obtain ⟨n,hn,pairs,hr,hlen,_,_,_,_,_,q,hread,hmin⟩ := h
  obtain ⟨hnval,hpairs⟩ := polynomial_partition_output_query_identifies P n pairs hr hlen
  subst n
  subst pairs
  rw [partition_real_dense_box_exact] at hmin
  change IsLeast P.constructedFirstCoordinates (q : ℝ) at hmin
  obtain ⟨A,hA,hfirst,hpart,hne,hbounded⟩ := P.constructed_hull_partition_threshold
  have heq : (q : ℝ) = 1/A.det := le_antisymm (hmin.2 hfirst.1) (hfirst.2 hmin.1)
  have hsat : input ∈ SAT.language ↔ P.HasPartition := by
    rw [← paper_partition_code_mem_language P,← hP]
    exact sat_partition_code_actual_polytime.2.2 input
  have hiff : q ≤ 1/P.threshold ↔ input ∈ SAT.language := by
    rw [hsat]
    have hc : (q : ℝ) ≤ ((1/P.threshold : ℚ) : ℝ) ↔ P.HasPartition := by
      simpa only [Rat.cast_div,Rat.cast_one,heq] using hpart.symm
    simpa only [Rat.cast_le] using hc
  have hv := (rational_parser_success_value_tail answer q [] hread).1
  rw [polynomialSATHullAnswer,pairFst_pair,pairSnd_pair,hP,
    polynomial_fraction_le_value,hv,polynomial_partition_hull_threshold_value]
  simpa only [firstBit,List.headD_cons,decide_eq_true_eq] using hiff

theorem exact_first_hull_endpoint_output_np_hard : NPHardOutputTask ExactFirstHullEndpointOutput := by
  have hs : PolynomialOneQueryReduction SAT.language ExactFirstHullEndpointOutput := by
    refine ⟨polynomialSATOutputQuery,polynomial_sat_output_query_mem_fp,
      polynomialSATHullAnswer,polynomial_sat_hull_answer_mem_fp,?_,polynomial_sat_first_hull_answer_correct⟩
    intro input
    obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
    simpa only [polynomialSATOutputQuery,hP] using partition_exact_first_hull_output_exists P
  intro L hL
  exact one_query_reduction_of_map (actual_binary_sat_np_complete.2 L hL) hs

#print axioms partition_exact_range_output_exists
#print axioms polynomial_sat_range_answer_correct
#print axioms exact_determinant_range_output_np_hard
#print axioms partition_exact_first_hull_output_exists
#print axioms polynomial_sat_first_hull_answer_correct
#print axioms exact_first_hull_endpoint_output_np_hard
end IV04.Paper.Computational
