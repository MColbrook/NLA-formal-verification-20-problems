module

public import NLA.IV04.PaperMatrixCoefficientInputDefinitions
public import NLA.IV04.PaperNaturalParserSemantics
public import NLA.IV04.PaperFractionCoefficientClearing
public import NLA.IV04.PaperCanonicalProduct
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem matrix_field_count_word_value (dimension : List Bool) :
    wordValue (matrixFieldCountWord dimension)=2*wordValue dimension*wordValue dimension+1 := by
  have hd : wordValue (false :: canonicalWordMultiply dimension dimension)=
      2*wordValue (canonicalWordMultiply dimension dimension) := by simp [wordValue,bitValue]
  have hone : wordValue [true]=1 := rfl
  simp only [matrixFieldCountWord,canonical_word_value,polynomial_word_add_value,hd,hone,
    canonical_word_multiply_value]
  ring

theorem matrix_field_count_word_length (dimension : List Bool) :
    (matrixFieldCountWord dimension).length ≤ 2*dimension.length+3 := by
  have hm := canonical_word_multiply_length dimension dimension
  have ha := polynomial_word_add_length (false :: canonicalWordMultiply dimension dimension) [true]
  have hc := canonical_word_length (polynomialWordAdd (false :: canonicalWordMultiply dimension dimension) [true])
  change (canonicalWord (polynomialWordAdd (false :: canonicalWordMultiply dimension dimension) [true])).length ≤ _
  simp only [List.length_cons,List.length_nil] at ha
  omega

theorem matrix_field_count_word_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixFieldCountWord (v 0) := by
  have hm := Cobham.comp₂ canonical_word_multiply_cobham
    (Cobham.proj (0 : Fin 1)) (Cobham.proj (0 : Fin 1))
  have hd := Cobham.comp (Cobham.bit false) fun _ : Fin 1 => hm
  have ha := Cobham.comp₂ polynomial_word_add_cobham hd (Cobham.const [true])
  exact (Cobham.comp canonical_word_cobham fun _ : Fin 1 => ha).of_eq fun _ => rfl

theorem matrix_field_count_word_mem_fp : matrixFieldCountWord ∈ FP :=
  CobhamFP_subset_FP matrix_field_count_word_cobham

theorem matrix_dimension_word_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDimensionWord (v 0) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.fstBlockFn (Cobham.sndBlockFn encoded_natural_parser_cobham)).of_eq fun _ => rfl

theorem unary_input_cobham_comp {n : ℕ} {f : List Bool → List Bool}
    {g : (Fin n → List Bool) → List Bool}
    (hf : Cobham fun v : Fin 1 → List Bool => f (v 0)) (hg : Cobham g) :
    Cobham fun v => f (g v) :=
  (Cobham.comp hf fun _ : Fin 1 => hg).of_eq fun _ => rfl

theorem input_pair_cobham_comp {n : ℕ} {left right : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) : Cobham fun v => pair (left v) (right v) :=
  (Cobham.comp₂ Cobham.pairing hl hr).of_eq fun _ => rfl

theorem matrix_rational_field_input_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixRationalFieldInput (v 0) := by
  have hp : Cobham fun v : Fin 1 → List Bool =>
      pairFst (pairSnd (encodedNaturalParser (v 0))) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn encoded_natural_parser_cobham)
  have ht : Cobham fun v : Fin 1 → List Bool =>
      pairSnd (pairSnd (encodedNaturalParser (v 0))) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn encoded_natural_parser_cobham)
  have hc := unary_input_cobham_comp matrix_field_count_word_cobham hp
  simpa only [matrixRationalFieldInput] using input_pair_cobham_comp hc ht

set_option maxHeartbeats 2000000 in
theorem encoded_matrix_coefficient_input_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixCoefficientInput (v 0) := by
  have hh : Cobham fun v : Fin 1 → List Bool => pairFst (encodedNaturalParser (v 0)) :=
    Cobham.fstBlockFn encoded_natural_parser_cobham
  have hc : Cobham fun v : Fin 1 → List Bool =>
      encodedRationalListClearing (matrixRationalFieldInput (v 0)) :=
    unary_input_cobham_comp encoded_rational_list_clearing_cobham matrix_rational_field_input_cobham
  have hf : Cobham fun v : Fin 1 → List Bool =>
      andBit (pairFst (encodedNaturalParser (v 0)))
        (pairFst (encodedRationalListClearing (matrixRationalFieldInput (v 0)))) :=
    Cobham.andFn hh (Cobham.fstBlockFn hc)
  have hr := input_pair_cobham_comp matrix_dimension_word_cobham (Cobham.sndBlockFn hc)
  simpa only [encodedMatrixCoefficientInput] using input_pair_cobham_comp hf hr

theorem encoded_matrix_coefficient_input_mem_fp : encodedMatrixCoefficientInput ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_coefficient_input_cobham

#print axioms encoded_matrix_coefficient_input_mem_fp
end IV04.Paper.Computational
