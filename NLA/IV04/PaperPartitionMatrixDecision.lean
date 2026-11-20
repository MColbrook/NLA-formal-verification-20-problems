module

public import NLA.IV04.PaperPartitionMatrixGeometry
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational

theorem rational_pair_fields_threshold_injective (pairs other : List (ℚ × ℚ))
    (threshold value : ℚ) (hlen : pairs.length=other.length)
    (h : pairs.flatMap (fun row => [row.1,row.2])++[threshold] =
      other.flatMap (fun row => [row.1,row.2])++[value]) :
    pairs=other ∧ threshold=value := by
  induction pairs generalizing other with
  | nil =>
    have he : other=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    subst other
    exact ⟨rfl,by simpa using h⟩
  | cons row rows ih =>
    cases other with
    | nil => simp at hlen
    | cons next rest =>
      have ht : rows.length=rest.length := by simpa using hlen
      simp only [List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append] at h
      have ha := List.cons.inj h
      have hb := List.cons.inj ha.2
      obtain ⟨hr,hv⟩ := ih rest ht hb.2
      have hp : row=next := Prod.ext ha.1 hb.1
      exact ⟨by rw [hp,hr],hv⟩

theorem polynomial_partition_matrix_language_iff (P : IV04.Paper.IntegerPartition) :
    polynomialPartitionMatrixCode P.inputCode ∈ rationalMatrixDeterminantDecisionLanguage ↔
      P.HasPartition := by
  have hread := polynomial_partition_matrix_code_read P []
  simp only [List.append_nil] at hread
  constructor
  · rintro ⟨n,pairs,threshold,hr,hsize,_,_,A,hA,hdet⟩
    have he := Option.some.inj (hr.symm.trans hread)
    have hn : n=P.layerCount := congrArg Prod.fst he
    subst n
    have hv : pairs.flatMap (fun row => [row.1,row.2])++[threshold] =
        (partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2])++[P.threshold] :=
      congrArg (fun z : ℕ × List ℚ × List Bool => z.2.1) he
    obtain ⟨hp,ht⟩ := rational_pair_fields_threshold_injective pairs
      (partitionMatrixEndpointPairs P) threshold P.threshold
      (hsize.trans (partition_endpoint_pairs_length P).symm) hv
    subst pairs
    subst threshold
    rw [partition_real_dense_box_exact] at hA
    exact (P.intervalBox_partition_threshold).mpr ⟨A,hA,hdet⟩
  · intro hp
    obtain ⟨A,hA,hdet⟩ := P.intervalBox_partition_threshold.mp hp
    refine ⟨P.layerCount,partitionMatrixEndpointPairs P,P.threshold,hread,
      partition_endpoint_pairs_length P,partition_endpoint_pairs_ordered P,
      partition_endpoint_pairs_support P,A,?_,hdet⟩
    rwa [partition_real_dense_box_exact]

#print axioms rational_pair_fields_threshold_injective
#print axioms polynomial_partition_matrix_language_iff
end IV04.Paper.Computational
