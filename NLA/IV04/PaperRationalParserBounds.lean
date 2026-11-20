module

public import NLA.IV04.PaperRationalParserPoly
public import NLA.IV04.PaperCountedMachineBounds
public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem natural_parser_payload_tail_budget (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  rw [natural_parser_payload,natural_parser_tail]
  simp only [List.length_take,List.length_drop,naturalParseRest,List.length_tail,List.length_drop]
  omega

theorem rational_parser_flag_boolean (input : List Bool) :
    Complexity.pairFst (encodedRationalParser input)=[true] ∨
      Complexity.pairFst (encodedRationalParser input)=[false] := by
  rw [rational_parser_flag,rational_parser_flag_stages]
  split_ifs <;> simp

theorem rational_parser_tail_length (input : List Bool) :
    (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))).length ≤ input.length := by
  rw [rational_parser_tail]
  have h1 := natural_parser_tail_length input.tail
  have h2 := natural_parser_tail_length
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input)))
  change (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length ≤ input.tail.length at h1
  change (Complexity.pairSnd (Complexity.pairSnd (rationalParserSecond input))).length ≤
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length at h2
  simp only [List.length_tail] at h1
  omega

theorem rational_parser_raw_payload_budget (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
      (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length ≤ input.length := by
  have h1 := natural_parser_payload_tail_budget input.tail
  have h2 := natural_parser_payload_length
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input)))
  change (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length ≤ input.tail.length at h1
  change (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length ≤
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length at h2
  simp only [List.length_tail] at h1
  omega

theorem rational_parser_fraction_length (input : List Bool) :
    (rationalParserFraction input).length ≤ 2*input.length+5 := by
  have hp := rational_parser_raw_payload_budget input
  have hn := signed_word_pack_length (Complexity.bitAt [] input)
    (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input)))
  have hd := canonical_word_length (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input)))
  rw [rationalParserFraction,normalize_fraction_word_cases]
  simp only [Complexity.pairFst_pair,Complexity.pairSnd_pair]
  split_ifs <;> simp only [Complexity.pair_length,List.length_cons,List.length_nil] <;> omega

theorem rational_parser_success_budget (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[true]) :
    (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
      (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))).length+3 ≤ input.length := by
  rw [rational_parser_flag,rational_parser_flag_stages] at h
  split_ifs at h with hi hp <;> simp at h
  have h1 := natural_parser_success_budget input.tail hp.1
  have h2 := natural_parser_success_budget
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))) hp.2
  change (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length+1 ≤ input.tail.length at h1
  change (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length+
    (Complexity.pairSnd (Complexity.pairSnd (rationalParserSecond input))).length+1 ≤
      (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst input))).length at h2
  rw [rational_parser_tail]
  simp only [List.length_tail] at h1
  omega

#print axioms rational_parser_success_budget
end IV04.Paper.Computational
