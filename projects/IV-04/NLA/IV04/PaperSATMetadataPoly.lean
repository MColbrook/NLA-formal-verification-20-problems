module

public import NLA.IV04.PaperSATMetadataDefinitions
public import NLA.IV04.PaperPayloadWordMaxPoly
public import NLA.IV04.PaperNestedPayloadCountPoly
public import NLA.IV04.PaperSATCNFParserPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

 theorem sat_clause_maximum_select_bound (input : List Bool) :
    (pairFst input).length ≤ 2*input.length+0 := by
  have h := pairFst_length_le input
  omega

 theorem polynomial_sat_clause_maximum_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATClauseMaximum (v 0) := by
  exact (polynomial_payload_word_max_cobham pairFst 0
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) sat_clause_maximum_select_bound).of_eq fun _ => rfl

 theorem polynomial_sat_clause_maximum_length (input : List Bool) :
    (polynomialSATClauseMaximum input).length ≤ 2*input.length+2 := by
  simpa [polynomialSATClauseMaximum] using
    polynomial_payload_word_max_length pairFst 0 sat_clause_maximum_select_bound input

 theorem polynomial_sat_formula_maximum_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATFormulaMaximum (v 0) := by
  exact (polynomial_payload_word_max_cobham polynomialSATClauseMaximum 2
    polynomial_sat_clause_maximum_cobham polynomial_sat_clause_maximum_length).of_eq fun _ => rfl

 theorem polynomial_sat_formula_maximum_length (input : List Bool) :
    (polynomialSATFormulaMaximum input).length ≤ 4*input.length+2 := by
  have h := polynomial_payload_word_max_length polynomialSATClauseMaximum 2
    polynomial_sat_clause_maximum_length input
  change (polynomialSATFormulaMaximum input).length ≤ _ at h
  omega

 theorem polynomial_sat_metadata_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATMetadata (v 0) := by
  have hv := Cobham.comp₂ polynomial_word_add_cobham polynomial_sat_formula_maximum_cobham
    (Cobham.const [true])
  have hl := Cobham.comp₂ polynomial_word_add_cobham polynomial_nested_payload_count_cobham
    (Cobham.const [true])
  exact (Cobham.comp₂ Cobham.pairing (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hv)
    (Cobham.comp₂ Cobham.pairing polynomial_payload_count_cobham
      (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hl))).of_eq fun _ => rfl

 theorem polynomial_sat_metadata_mem_fp : polynomialSATMetadata ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_metadata_cobham

 theorem polynomial_sat_input_metadata_mem_fp : polynomialSATInputMetadata ∈ FP := by
  have hp := FP_subset_CobhamFP polynomial_sat_cnf_parse_mem_fp
  have hm := Cobham.comp polynomial_sat_metadata_cobham fun _ : Fin 1 => Cobham.sndBlockFn hp
  exact CobhamFP_subset_FP ((Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn hp) hm).of_eq fun _ => rfl)

#print axioms polynomial_sat_input_metadata_mem_fp
#print axioms polynomial_sat_metadata_mem_fp
end IV04.Paper.Computational
