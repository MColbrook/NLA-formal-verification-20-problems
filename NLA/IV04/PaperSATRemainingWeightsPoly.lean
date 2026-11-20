module

public import NLA.IV04.PaperSATRemainingWeightsDefinitions
public import NLA.IV04.PaperSATLiteralDigitsPoly
public import NLA.IV04.PaperBoundedPayloadRepeatPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
 theorem polynomial_sat_clause_target_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATClauseTarget (v 0) := by
  unfold polynomialSATClauseTarget
  exact sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham
    (fun v : Fin 1 → List Bool => pairFst (polynomialSATMetadata (v 0)))
    (fun v : Fin 1 → List Bool => pairSnd (pairSnd (polynomialSATMetadata (v 0))))
    (sat_literal_cobham_fst _ polynomial_sat_metadata_cobham)
    (sat_literal_cobham_snd _ (sat_literal_cobham_snd _ polynomial_sat_metadata_cobham))
 theorem polynomial_sat_slack_digits_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATSlackDigits (v 0) := by
  have hb := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hq := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hp := sat_literal_cobham_unary polynomialSATCNFParse polynomial_sat_cnf_parse_cobham _ hb
  have hf := sat_literal_cobham_snd _ hp
  have hm := sat_literal_cobham_unary polynomialSATMetadata polynomial_sat_metadata_cobham _ hf
  have hu : Cobham fun v : Fin 1 → List Bool => polynomialSATVariableMarkers (v 0) :=
    FP_subset_CobhamFP polynomial_sat_variable_markers_mem_fp
  have hr : Cobham fun v : Fin 1 → List Bool => polynomialBoundedPayloadRepeat (v 0) :=
    FP_subset_CobhamFP polynomial_bounded_payload_repeat_mem_fp
  have hc := sat_literal_cobham_unary polynomialSATVariableMarkers hu _
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hb
      (sat_literal_cobham_binary pair Cobham.pairing _ _
        (sat_literal_cobham_fst _ (sat_literal_cobham_snd _ hm)) hq))
  have hz := sat_literal_cobham_unary polynomialBoundedPayloadRepeat hr _
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hb
      (sat_literal_cobham_binary pair Cobham.pairing _ (fun _ : Fin 1 → List Bool => [])
        (sat_literal_cobham_fst _ hm) (.const [])))
  unfold polynomialSATSlackDigits
  exact Cobham.appendFn hc hz
 theorem polynomial_sat_target_digits_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATTargetDigits (v 0) := by
  have hf := sat_literal_cobham_snd _ polynomial_sat_cnf_parse_cobham
  have hm := sat_literal_cobham_unary polynomialSATMetadata polynomial_sat_metadata_cobham _ hf
  have hk := sat_literal_cobham_unary polynomialSATClauseTarget polynomial_sat_clause_target_cobham _ hf
  have hr : Cobham fun v : Fin 1 → List Bool => polynomialBoundedPayloadRepeat (v 0) :=
    FP_subset_CobhamFP polynomial_bounded_payload_repeat_mem_fp
  have hc := sat_literal_cobham_unary polynomialBoundedPayloadRepeat hr _
    (sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => v 0) _ (.proj 0)
      (sat_literal_cobham_binary pair Cobham.pairing _ _
        (sat_literal_cobham_fst _ (sat_literal_cobham_snd _ hm)) hk))
  have hv := sat_literal_cobham_unary polynomialBoundedPayloadRepeat hr _
    (sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => v 0) _ (.proj 0)
      (sat_literal_cobham_binary pair Cobham.pairing _ (fun _ : Fin 1 → List Bool => [true])
        (sat_literal_cobham_fst _ hm) (.const [true])))
  unfold polynomialSATTargetDigits
  exact Cobham.appendFn hc hv
 theorem polynomial_sat_slack_weight_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATSlackWeight (v 0) := by
  have hb := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hp := sat_literal_cobham_unary polynomialSATCNFParse polynomial_sat_cnf_parse_cobham _ hb
  have hf := sat_literal_cobham_snd _ hp
  have hk := sat_literal_cobham_unary polynomialSATDigitBase polynomial_sat_digit_base_cobham _ hf
  have hh : Cobham fun v : Fin 1 → List Bool => polynomialWordListHorner (v 0) :=
    FP_subset_CobhamFP polynomial_word_list_horner_mem_fp
  have hi := sat_literal_cobham_binary pair Cobham.pairing _ _ hk polynomial_sat_slack_digits_cobham
  have he := sat_literal_cobham_unary polynomialWordListHorner hh _ hi
  unfold polynomialSATSlackWeight
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ he
 theorem polynomial_sat_target_weight_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATTargetWeight (v 0) := by
  have hf := sat_literal_cobham_snd _ polynomial_sat_cnf_parse_cobham
  have hk := sat_literal_cobham_unary polynomialSATDigitBase polynomial_sat_digit_base_cobham _ hf
  have hh : Cobham fun v : Fin 1 → List Bool => polynomialWordListHorner (v 0) :=
    FP_subset_CobhamFP polynomial_word_list_horner_mem_fp
  have hi := sat_literal_cobham_binary pair Cobham.pairing _ _ hk polynomial_sat_target_digits_cobham
  have he := sat_literal_cobham_unary polynomialWordListHorner hh _ hi
  unfold polynomialSATTargetWeight
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ he
 theorem polynomial_sat_slack_weight_mem_fp : polynomialSATSlackWeight ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_slack_weight_cobham
 theorem polynomial_sat_target_weight_mem_fp : polynomialSATTargetWeight ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_target_weight_cobham
#print axioms polynomial_sat_slack_weight_mem_fp
#print axioms polynomial_sat_target_weight_mem_fp
end IV04.Paper.Computational
