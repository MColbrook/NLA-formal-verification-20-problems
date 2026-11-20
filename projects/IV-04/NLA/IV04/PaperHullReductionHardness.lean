module

public import NLA.IV04.PaperHullReductionSemantics
public import NLA.IV04.PaperPartitionMatrixDecision
public import NLA.IV04.PaperSATMatrixHardness
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem polynomial_partition_hull_language_iff (P : IV04.Paper.IntegerPartition) :
    polynomialPartitionHullCode P.inputCode ∈ rationalMatrixHullDecisionLanguage ↔ P.HasPartition := by
  have hread := polynomial_partition_hull_code_read P []
  simp only [List.append_nil] at hread
  obtain ⟨A,hA,hfirst,hpart,hne,hbounded⟩ := P.constructed_hull_partition_threshold
  constructor
  · rintro ⟨n,hn,pairs,cutoff,hr,hsize,_,_,x,hx,hcut⟩
    have he := Option.some.inj (hr.symm.trans hread)
    have hnval : n = P.layerCount := congrArg Prod.fst he
    subst n
    have hv : pairs.flatMap (fun row => [row.1,row.2]) ++ [cutoff] =
        (partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2]) ++ [1/P.threshold] :=
      congrArg (fun z : ℕ × List ℚ × List Bool => z.2.1) he
    obtain ⟨hp,ht⟩ := rational_pair_fields_threshold_injective pairs
      (partitionMatrixEndpointPairs P) cutoff (1/P.threshold)
      (hsize.trans (partition_endpoint_pairs_length P).symm) hv
    subst pairs
    subst cutoff
    rw [partition_real_dense_box_exact] at hx
    change x ∈ P.constructedSolutions at hx
    have hvx : x ⟨0,hn⟩ ∈ P.constructedFirstCoordinates := ⟨x,hx,rfl⟩
    apply hpart.mpr
    have hc : x ⟨0,hn⟩ ≤ 1/(P.threshold : ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_one] using hcut
    exact (hfirst.2 hvx).trans hc
  · intro hp
    obtain ⟨x,hx,hvalue⟩ := hfirst.1
    refine ⟨P.layerCount,P.layerCount_pos,partitionMatrixEndpointPairs P,1/P.threshold,hread,
      partition_endpoint_pairs_length P,partition_endpoint_pairs_ordered P,
      partition_endpoint_pairs_support P,x,?_,?_⟩
    · rw [partition_real_dense_box_exact]
      exact hx
    · have hc := hpart.mp hp
      rw [← hvalue] at hc
      simpa only [Rat.cast_div,Rat.cast_one] using hc

theorem actual_binary_sat_hull_reduction (input : List Bool) :
    input ∈ SAT.language ↔ polynomialSATHullCode input ∈ rationalMatrixHullDecisionLanguage := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  rw [polynomialSATHullCode,hP,polynomial_partition_hull_language_iff,
    ← paper_partition_code_mem_language P,← hP]
  exact sat_partition_code_actual_polytime.2.2 input

theorem actual_binary_sat_hull_map_reduction : SAT.language ≤ₚ rationalMatrixHullDecisionLanguage :=
  ⟨polynomialSATHullCode,polynomial_sat_hull_code_mem_fp,actual_binary_sat_hull_reduction⟩

theorem actual_rational_interval_hull_np_hard : NPHard rationalMatrixHullDecisionLanguage :=
  actual_binary_sat_np_complete.2.of_reduction actual_binary_sat_hull_map_reduction

theorem actual_sat_hull_regular_bounded_unit_superdiagonal (input : List Bool) :
    ∃ (n : ℕ) (hn : 0 < n) (pairs : List (ℚ × ℚ)) (cutoff : ℚ),
      readMatrixRationals (polynomialSATHullCode input) =
        some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [cutoff],[]) ∧
      pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
      rationalDenseEndpointAll n 0 0 pairs ∧
      (∀ A ∈ realDenseIntervalBox n pairs, 0 < A.det ∧
        ∀ i j : Fin n, j.val = i.val+1 → A i j = 1) ∧
      (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)).Nonempty ∧
      Bornology.IsBounded (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  have hread := polynomial_partition_hull_code_read P []
  simp only [List.append_nil] at hread
  obtain ⟨A,hA,hfirst,hpart,hne,hbounded⟩ := P.constructed_hull_partition_threshold
  refine ⟨P.layerCount,P.layerCount_pos,partitionMatrixEndpointPairs P,1/P.threshold,?_,
    partition_endpoint_pairs_length P,partition_endpoint_pairs_ordered P,
    partition_endpoint_pairs_support P,?_,?_,?_⟩
  · simpa only [polynomialSATHullCode,hP] using hread
  · intro A hA
    rw [partition_real_dense_box_exact] at hA
    exact ⟨P.intervalBox_regular A hA,P.intervalBox_superdiagonal A hA⟩
  · rw [partition_real_dense_box_exact]
    exact hne
  · rw [partition_real_dense_box_exact]
    exact hbounded

#print axioms polynomial_partition_hull_language_iff
#print axioms actual_binary_sat_hull_reduction
#print axioms actual_binary_sat_hull_map_reduction
#print axioms actual_rational_interval_hull_np_hard
#print axioms actual_sat_hull_regular_bounded_unit_superdiagonal
end IV04.Paper.Computational
