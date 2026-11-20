module

public import NLA.IV04.PaperSubsetPartitionBuilderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper.Computational
open Complexity SATReduction
theorem verified_payload_natural_output_iterate_length : ∀ (k : ℕ) (rest output : List Bool),
  ((payloadNaturalOutputStep^[k]) (Complexity.pair rest output)).length ≤
      2*rest.length+output.length+2+k := payload_natural_output_iterate_length

theorem verified_polynomial_payload_naturals_mem_fp : polynomialPayloadNaturals ∈ FP := polynomial_payload_naturals_mem_fp

theorem verified_polynomial_payload_naturals_exact : ∀ (payloads : List (List Bool)),
  polynomialPayloadNaturals (payloadListCode payloads)=
      payloads.flatMap (fun w => IV04.Paper.naturalCode (wordValue w)) := polynomial_payload_naturals_exact

theorem verified_payload_natural_output_actual_polytime : polynomialPayloadNaturals ∈ Complexity.FP ∧
    ∀ payloads, polynomialPayloadNaturals (payloadListCode payloads)=
      payloads.flatMap (fun w => IV04.Paper.naturalCode (wordValue w)) := payload_natural_output_actual_polytime

theorem verified_polynomial_subset_partition_code_mem_fp : polynomialSubsetPartitionCode ∈ FP := polynomial_subset_partition_code_mem_fp

theorem verified_subset_partition_builder_weights_reindex : ∀ {n : ℕ} (w : Fin n → ℕ) (target : ℕ),
  subsetPartitionBuilderWeights w target =
      fun j => subsetPartitionWeights w target ((subsetPartitionBuilderIndex n).symm j) := subset_partition_builder_weights_reindex

theorem verified_subset_partition_builder_weights_positive : ∀ {n : ℕ} (w : Fin n → ℕ) (target : ℕ)
    (hw : ∀ i, 0<w i),
  ∀ j, 0<subsetPartitionBuilderWeights w target j := subset_partition_builder_weights_positive

theorem verified_actual_subset_builder_partition_iff : ∀ (n : ℕ) (w : Fin n → ℕ) (target : ℕ)
    (hw : ∀ i, 0<w i),
  (actualSubsetBuilderPartition n w target hw).HasPartition ↔ HasSubsetSum w target := actual_subset_builder_partition_iff

theorem verified_polynomial_subset_partition_code_exact : ∀ (n : ℕ) (w : Fin n → ℕ) (target : ℕ),
  polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target)=
      countedWeightCode (n+2) (subsetPartitionBuilderWeights w target) := polynomial_subset_partition_code_exact

theorem verified_subset_partition_builder_actual_polytime : polynomialSubsetPartitionCode ∈ Complexity.FP ∧
    ∀ (n : ℕ) (w : Fin n → ℕ) (target : ℕ) (hw : ∀ i, 0<w i),
      polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target)=
        (actualSubsetBuilderPartition n w target hw).inputCode ∧
      (polynomialSubsetPartitionCode (subsetPartitionBuilderInput n w target) ∈ positivePartitionLanguage ↔
        HasSubsetSum w target) := subset_partition_builder_actual_polytime

#print axioms IV04.Paper.Computational.verified_payload_natural_output_iterate_length
#print axioms IV04.Paper.Computational.verified_polynomial_payload_naturals_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_payload_naturals_exact
#print axioms IV04.Paper.Computational.verified_payload_natural_output_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_subset_partition_code_mem_fp
#print axioms IV04.Paper.Computational.verified_subset_partition_builder_weights_reindex
#print axioms IV04.Paper.Computational.verified_subset_partition_builder_weights_positive
#print axioms IV04.Paper.Computational.verified_actual_subset_builder_partition_iff
#print axioms IV04.Paper.Computational.verified_polynomial_subset_partition_code_exact
#print axioms IV04.Paper.Computational.verified_subset_partition_builder_actual_polytime
end IV04.Paper.Computational
end
