module

public import NLA.IV04.PaperFractionListDenominatorsPoly
public import NLA.IV04.PaperRationalListParserComplete
public import NLA.IV04.PaperWordListPositive
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem fraction_list_denominators_iterate_nil (k : ℕ) (output : List Bool) :
    (fractionListDenominatorsStep^[k]) (pair [] output)=pair [] output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,fraction_list_denominators_step_pair]; simp

theorem fraction_list_denominators_iterate_code (k : ℕ) (payloads output : List (List Bool))
    (h : payloads.length ≤ k) :
    (fractionListDenominatorsStep^[k]) (pair (payloadListCode payloads) (payloadListCode output))=
      pair [] (payloadListCode ((payloads.map pairSnd).reverse ++ output)) := by
  induction k generalizing payloads output with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,fraction_list_denominators_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,fraction_list_denominators_step_pair]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,pairFst_pair,pairSnd_pair]
      have hi := ih payloads (pairSnd payload :: output) ht
      simp only [payloadListCode] at hi
      rw [hi]
      simp [List.reverse_cons,List.append_assoc]

theorem fraction_list_denominators_code (payloads : List (List Bool)) :
    polynomialFractionListDenominators (payloadListCode payloads)=
      payloadListCode ((payloads.map pairSnd).reverse) := by
  have h := fraction_list_denominators_iterate_code (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simpa only [polynomialFractionListDenominators,fractionListDenominatorsState,payloadListCode,
    pairSnd_pair,List.append_nil] using congrArg pairSnd h

theorem rational_list_denominator_value (input : List Bool) :
    ∃ b ps rest, encodedRationalListParser input=pair [b] (pair (payloadListCode ps) rest) ∧
      (∀ w ∈ ps, 0 < wordValue (pairSnd w)) ∧
      wordValue (polynomialRationalListDenominator input)=((ps.map pairSnd).map wordValue).prod := by
  obtain ⟨b,ps,rest,he,hp⟩ := rational_list_parser_payload_shape input
  refine ⟨b,ps,rest,he,hp,?_⟩
  simp only [polynomialRationalListDenominator,he,pairFst_pair,pairSnd_pair,canonical_word_value,
    fraction_list_denominators_code,polynomial_word_list_product_value,List.map_reverse,List.prod_reverse]

theorem rational_list_denominator_positive (input : List Bool) :
    0 < wordValue (polynomialRationalListDenominator input) := by
  obtain ⟨b,ps,rest,he,hp,hv⟩ := rational_list_denominator_value input
  rw [hv]
  have h := (payload_product_positive (ps.map pairSnd)).mpr (by
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact hp a ha)
  exact h

theorem counted_output_length_le (state : List Bool) : (countedOutput state).length ≤ state.length := by
  change (pairSnd (pairSnd (pairSnd state))).length ≤ state.length
  exact (pairSnd_length_le _).trans ((pairSnd_length_le _).trans (pairSnd_length_le _))

theorem polynomial_word_list_product_length (input : List Bool) :
    (polynomialWordListProduct input).length ≤ 2*input.length+3 := by
  have h := word_list_product_iterate_length input.length input [true]
  have hs := pairSnd_length_le (wordListProductState input)
  simp only [List.length_cons,List.length_nil] at h
  exact hs.trans (by simpa only [wordListProductState] using h)

theorem rational_list_denominator_length (input : List Bool) :
    (polynomialRationalListDenominator input).length ≤
      8*(2*input.length+8+input.length*(4*input.length+12))+7 := by
  let output := pairFst (pairSnd (encodedRationalListParser input))
  have he : output=countedOutput (rationalListState input) := by
    simp only [output,encodedRationalListParser,pairFst_pair,pairSnd_pair]
  have ho := counted_output_length_le (rationalListState input)
  have hstate := rational_list_state_length input
  have hd := fraction_list_denominators_output_length output
  have hp := polynomial_word_list_product_length (polynomialFractionListDenominators output)
  have hc := canonical_word_length (polynomialWordListProduct (polynomialFractionListDenominators output))
  change (canonicalWord (polynomialWordListProduct (polynomialFractionListDenominators output))).length ≤ _
  rw [←he] at ho
  omega

theorem rational_list_denominator_actual_polytime : polynomialRationalListDenominator ∈ FP ∧
    ∀ input, 0 < wordValue (polynomialRationalListDenominator input) ∧
      (polynomialRationalListDenominator input).length ≤
        8*(2*input.length+8+input.length*(4*input.length+12))+7 :=
  ⟨rational_list_denominator_mem_fp,fun input =>
    ⟨rational_list_denominator_positive input,rational_list_denominator_length input⟩⟩

#print axioms rational_list_denominator_actual_polytime
end IV04.Paper.Computational
