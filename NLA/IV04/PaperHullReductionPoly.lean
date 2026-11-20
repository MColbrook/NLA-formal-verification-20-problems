module

public import NLA.IV04.PaperHullReductionDefinitions
public import NLA.IV04.PaperPartitionMatrixPoly
public import NLA.IV04.PaperSATMatrixHardness
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_partition_hull_threshold_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPartitionHullThresholdFraction (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionSquaredScale polynomial_partition_squared_scale_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false)
    (fun v : Fin 1 → List Bool => polynomialPartitionSquaredScale (v 0)) h0
  have h2 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham
    (fun v : Fin 1 → List Bool => false :: polynomialPartitionSquaredScale (v 0))
    (fun _ : Fin 1 → List Bool => [true]) h1 (.const [true])
  have h3 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false)
    (fun v : Fin 1 → List Bool => false :: polynomialPartitionSquaredScale (v 0)) h1
  have h4 := sat_literal_cobham_binary pair Cobham.pairing
    (fun v : Fin 1 → List Bool => false :: (false :: polynomialPartitionSquaredScale (v 0)))
    (fun v : Fin 1 → List Bool => polynomialWordSub (false :: polynomialPartitionSquaredScale (v 0)) [true]) h3 h2
  unfold polynomialPartitionHullThresholdFraction
  exact h4

theorem polynomial_partition_hull_threshold_mem_fp : polynomialPartitionHullThresholdFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_hull_threshold_cobham

theorem polynomial_partition_hull_code_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPartitionHullCode (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have h1 := sat_literal_cobham_unary canonicalWordCode canonical_word_code_cobham
    (fun v : Fin 1 → List Bool => polynomialPartitionLayerCount (v 0)) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionEndpointTable polynomial_partition_endpoint_table_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have h3 := Cobham.appendFn h1 h2
  have h4 := sat_literal_cobham_unary polynomialPartitionHullThresholdFraction polynomial_partition_hull_threshold_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have h5 := sat_literal_cobham_unary polynomialFractionOutput polynomial_fraction_output_cobham
    (fun v : Fin 1 → List Bool => polynomialPartitionHullThresholdFraction (v 0)) h4
  unfold polynomialPartitionHullCode
  exact Cobham.appendFn h3 h5

theorem polynomial_partition_hull_code_mem_fp : polynomialPartitionHullCode ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_hull_code_cobham

theorem polynomial_sat_hull_code_mem_fp : polynomialSATHullCode ∈ FP := by
  have hs := FP_subset_CobhamFP polynomial_sat_partition_code_mem_fp
  exact CobhamFP_subset_FP ((Cobham.comp polynomial_partition_hull_code_cobham
    (fun _ : Fin 1 => hs)).of_eq (fun _ => rfl))

#print axioms polynomial_partition_hull_threshold_mem_fp
#print axioms polynomial_partition_hull_code_mem_fp
#print axioms polynomial_sat_hull_code_mem_fp
end IV04.Paper.Computational
