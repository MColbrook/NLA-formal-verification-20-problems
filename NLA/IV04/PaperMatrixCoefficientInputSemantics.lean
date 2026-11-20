module

public import NLA.IV04.PaperMatrixCoefficientInputPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem natural_parser_success_shape (input : List Bool) (n : ℕ) (tail : List Bool)
    (h : IV04.Paper.readNatural input=some (n,tail)) :
    ∃ payload, encodedNaturalParser input=pair [true] (pair payload tail) ∧ wordValue payload=n := by
  have he := natural_parser_exact input
  rw [h] at he
  by_cases hf : pairFst (encodedNaturalParser input)=[true]
  · simp only [hf,if_true,Option.some.injEq,Prod.mk.injEq] at he
    refine ⟨pairFst (pairSnd (encodedNaturalParser input)),?_,he.1⟩
    have hp : encodedNaturalParser input=pair (pairFst (encodedNaturalParser input))
        (pair (pairFst (pairSnd (encodedNaturalParser input))) (pairSnd (pairSnd (encodedNaturalParser input)))) := by
      simp only [encodedNaturalParser,pairFst_pair,pairSnd_pair]
    calc
      encodedNaturalParser input = _ := hp
      _ = pair [true] (pair (pairFst (pairSnd (encodedNaturalParser input))) tail) := by rw [hf,he.2]
  · simp [hf] at he

theorem natural_parser_failure_flag (input : List Bool) (h : IV04.Paper.readNatural input=none) :
    pairFst (encodedNaturalParser input)=[false] := by
  have he := natural_parser_exact input
  rw [h] at he
  obtain hf | hf := natural_parser_flag_boolean input
  · simp [hf] at he
  · exact hf

theorem read_rationals_result_length (count : ℕ) (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals count input=some (values,tail)) : values.length=count := by
  induction count generalizing input values tail with
  | zero =>
    have he : []=values ∧ input=tail := by simpa only [readRationals,Option.some.injEq,Prod.mk.injEq] using h
    rw [←he.1]
    rfl
  | succ count ih =>
    cases hn : IV04.Paper.readRational input with
    | none => simp [readRationals,hn] at h
    | some result =>
      obtain ⟨q,rest⟩ := result
      cases hr : readRationals count rest with
      | none => simp [readRationals,hn,hr] at h
      | some result =>
        obtain ⟨qs,last⟩ := result
        have he : q::qs=values ∧ last=tail := by simpa [readRationals,hn,hr] using h
        rw [←he.1,List.length_cons,ih rest qs last hr]

theorem matrix_rational_field_input_count (input : List Bool) :
    wordValue (pairFst (matrixRationalFieldInput input))=
      2*wordValue (pairFst (pairSnd (encodedNaturalParser input)))*
        wordValue (pairFst (pairSnd (encodedNaturalParser input)))+1 := by
  simp only [matrixRationalFieldInput,pairFst_pair,matrix_field_count_word_value]

theorem matrix_rational_field_input_tail (input : List Bool) :
    pairSnd (matrixRationalFieldInput input)=pairSnd (pairSnd (encodedNaturalParser input)) := by
  simp only [matrixRationalFieldInput,pairSnd_pair]

theorem matrix_coefficient_input_correct (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput input=pair [true]
        (pair dimension (pair denominator (pair (payloadListCode coefficients) tail))) ∧
      wordValue dimension=n ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*n*n+1 := by
  cases hn : IV04.Paper.readNatural input with
  | none => simp [readMatrixRationals,hn] at h
  | some result =>
    obtain ⟨dim,rest⟩ := result
    cases hr : readRationals (2*dim*dim+1) rest with
    | none => simp [readMatrixRationals,hn,hr] at h
    | some result =>
      obtain ⟨qs,last⟩ := result
      have he : dim=n ∧ qs=values ∧ last=tail := by simpa [readMatrixRationals,hn,hr] using h
      obtain ⟨rfl,rfl,rfl⟩ := he
      obtain ⟨payload,hp,hv⟩ := natural_parser_success_shape input dim rest hn
      have hf : readRationals (wordValue (pairFst (matrixRationalFieldInput input)))
          (pairSnd (matrixRationalFieldInput input))=some (qs,last) := by
        simp only [matrix_rational_field_input_count,matrix_rational_field_input_tail,hp,pairFst_pair,pairSnd_pair,hv]
        exact hr
      obtain ⟨denominator,coefficients,hc,hd,hq,hl⟩ := rational_list_clearing_correct
        (matrixRationalFieldInput input) qs last hf
      refine ⟨canonicalWord payload,denominator,coefficients,?_,?_,hd,hq,?_⟩
      · simp only [encodedMatrixCoefficientInput,hp,hc,pairFst_pair,pairSnd_pair,matrixDimensionWord]
        simp [andBit,caseBit₀]
      · rw [canonical_word_value,hv]
      · rw [hl,read_rationals_result_length _ _ _ _ hr]

theorem matrix_coefficient_input_failure (input : List Bool) (h : readMatrixRationals input=none) :
    pairFst (encodedMatrixCoefficientInput input)=[false] := by
  cases hn : IV04.Paper.readNatural input with
  | none =>
    have hf := natural_parser_failure_flag input hn
    simp [encodedMatrixCoefficientInput,hf,andBit,caseBit₀]
  | some result =>
    obtain ⟨dim,rest⟩ := result
    have hr : readRationals (2*dim*dim+1) rest=none := by
      cases hq : readRationals (2*dim*dim+1) rest with
      | none => rfl
      | some result => simp [readMatrixRationals,hn,hq] at h
    obtain ⟨payload,hp,hv⟩ := natural_parser_success_shape input dim rest hn
    have hfield : readRationals (wordValue (pairFst (matrixRationalFieldInput input)))
        (pairSnd (matrixRationalFieldInput input))=none := by
      simp only [matrix_rational_field_input_count,matrix_rational_field_input_tail,hp,pairFst_pair,pairSnd_pair,hv]
      exact hr
    have hf := rational_list_clearing_failure (matrixRationalFieldInput input) hfield
    simp [encodedMatrixCoefficientInput,hp,hf,andBit,caseBit₀]

theorem matrix_coefficient_input_valid_iff (input : List Bool) :
    pairFst (encodedMatrixCoefficientInput input)=[true] ↔
      ∃ n values tail, readMatrixRationals input=some (n,values,tail) := by
  constructor
  · intro hf
    cases hr : readMatrixRationals input with
    | none => rw [matrix_coefficient_input_failure input hr] at hf; cases hf
    | some result => obtain ⟨n,values,tail⟩ := result; exact ⟨n,values,tail,rfl⟩
  · rintro ⟨n,values,tail,h⟩
    obtain ⟨dimension,denominator,coefficients,he,_,_,_,_⟩ := matrix_coefficient_input_correct input n values tail h
    rw [he,pairFst_pair]

theorem read_matrix_rationals_codes (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : values.length=2*n*n+1) :
    readMatrixRationals (IV04.Paper.naturalCode n ++ (values.flatMap IV04.Paper.rationalCode ++ tail))=
      some (n,values,tail) := by
  simp only [readMatrixRationals,IV04.Paper.read_natural_code,bind,Option.bind_some]
  rw [←h,read_rationals_codes]
  rfl

theorem matrix_coefficient_input_actual_polytime : encodedMatrixCoefficientInput ∈ FP ∧
    ∀ input n values tail, readMatrixRationals input=some (n,values,tail) →
      ∃ dimension denominator coefficients,
        encodedMatrixCoefficientInput input=pair [true]
          (pair dimension (pair denominator (pair (payloadListCode coefficients) tail))) ∧
        wordValue dimension=n ∧ 0 < wordValue denominator ∧
        coefficients.map (fun w => (signedWordValue w : ℚ))=
          values.map (fun q => q*(wordValue denominator : ℚ)) ∧
        coefficients.length=2*n*n+1 :=
  ⟨encoded_matrix_coefficient_input_mem_fp,matrix_coefficient_input_correct⟩

#print axioms matrix_coefficient_input_actual_polytime
end IV04.Paper.Computational
