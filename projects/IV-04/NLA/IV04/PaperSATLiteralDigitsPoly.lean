module

public import NLA.IV04.PaperSATLiteralDigitsDefinitions
public import NLA.IV04.PaperSATVariableMarkersPoly
public import NLA.IV04.PaperSATClauseCoefficientsPoly
public import NLA.IV04.PaperSATMetadataPoly
public import NLA.IV04.PaperWordListHornerPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
/-- Keep the function arguments explicit when composing large concrete programs. -/
theorem sat_literal_cobham_unary {n : ℕ} (f : List Bool → List Bool)
    (hf : Cobham fun w : Fin 1 → List Bool => f (w 0))
    (g : (Fin n → List Bool) → List Bool) (hg : Cobham g) :
    Cobham fun v : Fin n → List Bool => f (g v) := by
  exact (Cobham.comp (f := fun w : Fin 1 → List Bool => f (w 0))
    (gs := fun _ : Fin 1 => g) hf (fun _ => hg)).of_eq fun _ => rfl
theorem sat_literal_cobham_binary {n : ℕ} (f : List Bool → List Bool → List Bool)
    (hf : Cobham fun w : Fin 2 → List Bool => f (w 0) (w 1))
    (g h : (Fin n → List Bool) → List Bool) (hg : Cobham g) (hh : Cobham h) :
    Cobham fun v : Fin n → List Bool => f (g v) (h v) := by
  exact (Cobham.comp₂ (f := fun w : Fin 2 → List Bool => f (w 0) (w 1))
    (g₀ := g) (g₁ := h) hf hg hh).of_eq fun _ => rfl
theorem sat_literal_cobham_fst {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (hg : Cobham g) : Cobham fun v : Fin n → List Bool => pairFst (g v) :=
  sat_literal_cobham_unary pairFst (FP_subset_CobhamFP fstBlock_mem_FP) g hg
theorem sat_literal_cobham_snd {n : ℕ} (g : (Fin n → List Bool) → List Bool)
    (hg : Cobham g) : Cobham fun v : Fin n → List Bool => pairSnd (g v) :=
  sat_literal_cobham_unary pairSnd (FP_subset_CobhamFP sndBlock_mem_FP) g hg
 theorem polynomial_sat_literal_digits_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATLiteralDigits (v 0) := by
  have hb : Cobham fun v : Fin 1 → List Bool => pairFst (v 0) :=
    sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hq : Cobham fun v : Fin 1 → List Bool => pairSnd (v 0) :=
    sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hp := sat_literal_cobham_unary polynomialSATCNFParse polynomial_sat_cnf_parse_cobham
    (fun v : Fin 1 → List Bool => pairFst (v 0)) hb
  have hf := sat_literal_cobham_snd
    (fun v : Fin 1 → List Bool => polynomialSATCNFParse (pairFst (v 0))) hp
  have hm := sat_literal_cobham_unary polynomialSATMetadata polynomial_sat_metadata_cobham
    (fun v : Fin 1 → List Bool => pairSnd (polynomialSATCNFParse (pairFst (v 0)))) hf
  have hc := sat_literal_cobham_unary polynomialSATClauseCoefficients
    polynomial_sat_clause_coefficients_cobham
    (fun v : Fin 1 → List Bool => pair
      (pairSnd (polynomialSATCNFParse (pairFst (v 0)))) (pairSnd (v 0)))
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hf hq)
  have hu : Cobham fun v : Fin 1 → List Bool => polynomialSATVariableMarkers (v 0) :=
    FP_subset_CobhamFP polynomial_sat_variable_markers_mem_fp
  have hv := sat_literal_cobham_unary polynomialSATVariableMarkers hu
    (fun v : Fin 1 → List Bool => pair (pairFst (v 0))
      (pair (pairFst (polynomialSATMetadata
        (pairSnd (polynomialSATCNFParse (pairFst (v 0)))))) (pairFst (pairSnd (v 0)))))
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hb
      (sat_literal_cobham_binary pair Cobham.pairing _ _
        (sat_literal_cobham_fst _ hm) (sat_literal_cobham_fst _ hq)))
  unfold polynomialSATLiteralDigits
  exact Cobham.appendFn hc hv
 theorem polynomial_sat_literal_digits_mem_fp : polynomialSATLiteralDigits ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_literal_digits_cobham
 theorem polynomial_sat_digit_base_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATDigitBase (v 0) := by
  have ht := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham
    (fun v : Fin 1 → List Bool => pairFst (polynomialSATMetadata (v 0)))
    (fun v : Fin 1 → List Bool => pairSnd (pairSnd (polynomialSATMetadata (v 0))))
    (sat_literal_cobham_fst _ polynomial_sat_metadata_cobham)
    (sat_literal_cobham_snd _ (sat_literal_cobham_snd _ polynomial_sat_metadata_cobham))
  have hm := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham
    _ (fun _ : Fin 1 → List Bool => [false,false,true]) ht (.const [false,false,true])
  have ha := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham
    _ (fun _ : Fin 1 → List Bool => [true,true]) hm (.const [true,true])
  unfold polynomialSATDigitBase
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ ha
 theorem polynomial_sat_literal_weight_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATLiteralWeight (v 0) := by
  have hp := sat_literal_cobham_unary polynomialSATCNFParse polynomial_sat_cnf_parse_cobham
    (fun v : Fin 1 → List Bool => pairFst (v 0))
    (sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0))
  have hf := sat_literal_cobham_snd _ hp
  have hb := sat_literal_cobham_unary polynomialSATDigitBase polynomial_sat_digit_base_cobham _ hf
  have hh : Cobham fun v : Fin 1 → List Bool => polynomialWordListHorner (v 0) :=
    FP_subset_CobhamFP polynomial_word_list_horner_mem_fp
  have hi := sat_literal_cobham_binary pair Cobham.pairing _ _ hb polynomial_sat_literal_digits_cobham
  have he := sat_literal_cobham_unary polynomialWordListHorner hh _ hi
  unfold polynomialSATLiteralWeight
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ he
 theorem polynomial_sat_literal_weight_mem_fp : polynomialSATLiteralWeight ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_literal_weight_cobham
#print axioms polynomial_sat_literal_digits_mem_fp
#print axioms polynomial_sat_literal_weight_mem_fp
end IV04.Paper.Computational
