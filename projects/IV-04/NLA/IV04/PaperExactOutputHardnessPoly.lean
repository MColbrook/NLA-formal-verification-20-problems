module

public import NLA.IV04.PaperExactOutputHardnessDefinitions
public import NLA.IV04.PaperHullReductionPoly
public import NLA.IV04.PaperRationalParserPoly
public import NLA.IV04.PaperSignedOrderPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_partition_output_query_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPartitionOutputQuery (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have h1 := sat_literal_cobham_unary canonicalWordCode canonical_word_code_cobham
    (fun v : Fin 1 → List Bool => polynomialPartitionLayerCount (v 0)) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionEndpointTable polynomial_partition_endpoint_table_cobham
    (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  unfold polynomialPartitionOutputQuery
  exact Cobham.appendFn (Cobham.appendFn h1 h2) (.const (IV04.Paper.rationalCode 0))

theorem polynomial_sat_output_query_mem_fp : polynomialSATOutputQuery ∈ FP := by
  have hs := FP_subset_CobhamFP polynomial_sat_partition_code_mem_fp
  exact CobhamFP_subset_FP ((Cobham.comp polynomial_partition_output_query_cobham
    (fun _ : Fin 1 => hs)).of_eq (fun _ => rfl))

theorem polynomial_sat_range_answer_mem_fp : polynomialSATRangeAnswer ∈ FP := by
  have hs := FP_subset_CobhamFP polynomial_sat_partition_code_mem_fp
  have hp := (Cobham.comp hs (fun _ : Fin 1 => Cobham.fstBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl)
  have ht := (Cobham.comp polynomial_partition_threshold_fraction_cobham (fun _ : Fin 1 => hp)).of_eq (fun _ => rfl)
  have hfirst := (Cobham.comp encoded_rational_parser_cobham
    (fun _ : Fin 1 => Cobham.sndBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl)
  have htail := Cobham.sndBlockFn (Cobham.sndBlockFn hfirst)
  have hmax := (Cobham.comp rational_parser_fraction_cobham (fun _ : Fin 1 => htail)).of_eq (fun _ => rfl)
  exact CobhamFP_subset_FP ((Cobham.comp₂ polynomial_fraction_le_cobham ht hmax).of_eq (fun _ => rfl))

theorem polynomial_sat_hull_answer_mem_fp : polynomialSATHullAnswer ∈ FP := by
  have hs := FP_subset_CobhamFP polynomial_sat_partition_code_mem_fp
  have hp := (Cobham.comp hs (fun _ : Fin 1 => Cobham.fstBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl)
  have ht := (Cobham.comp polynomial_partition_hull_threshold_cobham (fun _ : Fin 1 => hp)).of_eq (fun _ => rfl)
  have hmin := (Cobham.comp rational_parser_fraction_cobham
    (fun _ : Fin 1 => Cobham.sndBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl)
  exact CobhamFP_subset_FP ((Cobham.comp₂ polynomial_fraction_le_cobham hmin ht).of_eq (fun _ => rfl))

theorem one_query_reduction_of_map {L K : Set (List Bool)}
    {task : List Bool → List Bool → Prop}
    (hmap : L ≤ₚ K) (hquery : PolynomialOneQueryReduction K task) :
    PolynomialOneQueryReduction L task := by
  obtain ⟨f,hf,hcorrect⟩ := hmap
  obtain ⟨query,hq,finish,hg,hne,hsound⟩ := hquery
  let lift : List Bool → List Bool := fun packed => pair (f (pairFst packed)) (pairSnd packed)
  have hfc := FP_subset_CobhamFP hf
  have hlift : lift ∈ FP := by
    exact CobhamFP_subset_FP ((Cobham.comp₂ Cobham.pairing
      ((Cobham.comp hfc (fun _ : Fin 1 => Cobham.fstBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl))
      (Cobham.sndBlockFn (.proj (0 : Fin 1)))).of_eq (fun _ => rfl))
  refine ⟨query ∘ f,mem_FP_comp hf hq,finish ∘ lift,mem_FP_comp hlift hg,?_,?_⟩
  · intro input
    exact hne (f input)
  · intro input answer h
    simp only [Function.comp_apply,lift,pairFst_pair,pairSnd_pair]
    exact (hsound (f input) answer h).trans (hcorrect input).symm

#print axioms polynomial_sat_output_query_mem_fp
#print axioms polynomial_sat_range_answer_mem_fp
#print axioms polynomial_sat_hull_answer_mem_fp
#print axioms one_query_reduction_of_map
end IV04.Paper.Computational
