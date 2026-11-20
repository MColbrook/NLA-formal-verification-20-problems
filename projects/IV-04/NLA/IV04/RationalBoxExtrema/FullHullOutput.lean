module

public import NLA.IV04.RationalBoxExtrema.Constructed
public import NLA.IV04.PaperFullHullProjectionDefinitions
public import NLA.IV04.PaperExactOutputHardnessSemantics
public import Mathlib.Data.List.GetD

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema
open Reference.IV04AffinePolyhedronSteps

theorem regular_positive_box_endpoint_list {n : ℕ} (hn : 0 < n)
    (B : IV04.Paper.RationalMatrixBox n)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) :
    ∃ bounds : List (ℚ × ℚ), bounds.length = n ∧ ∀ j : Fin n,
      IsLeast ((fun x : Fin n → ℝ => x j) ''
        IV04.Paper.positiveSolutions n hn B.realizations)
        ((bounds.getD j.val (0,0)).1 : ℝ) ∧
      IsGreatest ((fun x : Fin n → ℝ => x j) ''
        IV04.Paper.positiveSolutions n hn B.realizations)
        ((bounds.getD j.val (0,0)).2 : ℝ) := by
  classical
  obtain ⟨lo,hi,h⟩ := regular_positive_box_endpoint_functions hn B hd
  let bounds : List (ℚ × ℚ) := List.ofFn (fun j : Fin n => (lo j,hi j))
  refine ⟨bounds,by simp [bounds],?_⟩
  intro j
  have hget : bounds.getD j.val (0,0) = (lo j,hi j) := by
    simp [bounds, List.getD, List.getElem?_ofFn, j.isLt]
  rw [hget]
  exact h j

theorem partition_exact_full_hull_output_exists (P : IV04.Paper.IntegerPartition) :
    ∃ answer, IV04.Paper.Computational.ExactFullHullOutput
      (IV04.Paper.Computational.polynomialPartitionOutputQuery P.inputCode) answer := by
  classical
  obtain ⟨bounds,hlen,hbounds⟩ := regular_positive_box_endpoint_list P.layerCount_pos
    P.intervalBox (fun A hA => ne_of_gt (P.intervalBox_regular A hA))
  obtain ⟨A,hA,hmax,hfirst,hne,hbounded⟩ := P.constructed_hull_endpoint
  refine ⟨bounds.flatMap (fun row => IV04.Paper.rationalCode row.1 ++
    IV04.Paper.rationalCode row.2),P.layerCount,P.layerCount_pos,
    IV04.Paper.Computational.partitionMatrixEndpointPairs P,bounds,?_,
    IV04.Paper.Computational.partition_endpoint_pairs_length P,
    IV04.Paper.Computational.partition_endpoint_pairs_ordered P,
    IV04.Paper.Computational.partition_endpoint_pairs_support P,?_,?_,?_,hlen,rfl,?_⟩
  · simpa only [List.append_nil] using
      IV04.Paper.Computational.polynomial_partition_output_query_read P []
  · intro B hB
    rw [IV04.Paper.Computational.partition_real_dense_box_exact] at hB
    exact ⟨ne_of_gt (P.intervalBox_regular B hB),P.intervalBox_superdiagonal B hB⟩
  · rw [IV04.Paper.Computational.partition_real_dense_box_exact]
    exact hne
  · rw [IV04.Paper.Computational.partition_real_dense_box_exact]
    exact hbounded
  · rw [IV04.Paper.Computational.partition_real_dense_box_exact]
    exact hbounds

#print axioms regular_positive_box_endpoint_list
#print axioms partition_exact_full_hull_output_exists
end Reference.IV04RationalBoxExtrema
