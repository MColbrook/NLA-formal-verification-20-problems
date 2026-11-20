module

public import NLA.IV04.PaperSubsetPartitionBuilderPoly
public import NLA.IV04.PaperPayloadNaturalOutputSemantics
public import NLA.IV04.PaperWordListSumSemantics
public import NLA.IV04.PaperSATPartitionCode
public import NLA.IV04.PaperEncoding
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IV04.Paper.Computational
open SATReduction

private theorem builder_word_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

theorem subset_partition_builder_weights_reindex {n : ℕ} (w : Fin n → ℕ) (target : ℕ) :
    subsetPartitionBuilderWeights w target =
      fun j => subsetPartitionWeights w target ((subsetPartitionBuilderIndex n).symm j) := by
  have he : ∀ i, subsetPartitionBuilderWeights w target (subsetPartitionBuilderIndex n i)=
      subsetPartitionWeights w target i := by
    intro i
    cases i with
    | inl i => simp [subsetPartitionBuilderWeights,subsetPartitionBuilderIndex,subsetPartitionWeights]
    | inr b => cases b <;> simp [subsetPartitionBuilderWeights,subsetPartitionBuilderIndex,
        subsetPartitionWeights,boolFinTwo]
  funext j
  simpa only [Equiv.apply_symm_apply] using he ((subsetPartitionBuilderIndex n).symm j)

theorem subset_partition_builder_weights_positive {n : ℕ} (w : Fin n → ℕ) (target : ℕ)
    (hw : ∀ i, 0<w i) : ∀ j, 0<subsetPartitionBuilderWeights w target j := by
  rw [subset_partition_builder_weights_reindex]
  exact fun j => subset_partition_weights_positive w target hw _

theorem actual_subset_builder_partition_iff (n : ℕ) (w : Fin n → ℕ) (target : ℕ)
    (hw : ∀ i, 0<w i) :
    (actualSubsetBuilderPartition n w target hw).HasPartition ↔ HasSubsetSum w target := by
  rw [paper_partition_exact_signed]
  change SignedPartition (subsetPartitionBuilderWeights w target) ↔ HasSubsetSum w target
  rw [subset_partition_builder_weights_reindex,signed_partition_reindex,subset_partition_iff]

theorem polynomial_subset_partition_code_exact (n : ℕ) (w : Fin n → ℕ) (target : ℕ) :
    polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target)=
      countedWeightCode (n+2) (subsetPartitionBuilderWeights w target) := by
  have hmap : ∀ l : List ℕ, (l.map Nat.bits).map wordValue=l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons,builder_word_bits_value,ih]
  have hsum : wordValue (polynomialWordListSum (payloadListCode ((List.ofFn w).map Nat.bits)))=
      ∑ i, w i := by
    simpa only [hmap,List.sum_ofFn]
      using polynomial_word_list_sum_value ((List.ofFn w).map Nat.bits)
  have hlist : List.ofFn (subsetPartitionBuilderWeights w target)=
      List.ofFn w ++ [(∑ i, w i)+2*target+1,2*(∑ i, w i)+1] := by
    rw [subsetPartitionBuilderWeights,List.ofFn_fin_append]
    congr 1
  simp only [polynomialSubsetPartitionCode,subsetPartitionBuilderInput,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,canonical_word_code_exact,
    polynomial_word_add_value,builder_word_bits_value,hsum,polynomial_payload_naturals_exact,
    List.flatMap_map]
  simp only [countedWeightCode,hlist,List.flatMap_append,List.flatMap_cons,List.flatMap_nil]
  simp [wordValue,bitValue,List.append_assoc,Nat.add_assoc,two_mul]

theorem subset_partition_builder_actual_polytime : polynomialSubsetPartitionCode ∈ Complexity.FP ∧
    ∀ (n : ℕ) (w : Fin n → ℕ) (target : ℕ) (hw : ∀ i, 0<w i),
      polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target)=
        (actualSubsetBuilderPartition n w target hw).inputCode ∧
      (polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target) ∈ positivePartitionLanguage ↔
        HasSubsetSum w target) := by
  refine ⟨polynomial_subset_partition_code_mem_fp,?_⟩
  intro n w target hw
  have hc : polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target)=
      (actualSubsetBuilderPartition n w target hw).inputCode := polynomial_subset_partition_code_exact n w target
  exact ⟨hc,by rw [hc,paper_partition_code_mem_language,actual_subset_builder_partition_iff]⟩

#print axioms subset_partition_builder_weights_reindex
#print axioms polynomial_subset_partition_code_exact
#print axioms subset_partition_builder_actual_polytime
end IV04.Paper.Computational
end
