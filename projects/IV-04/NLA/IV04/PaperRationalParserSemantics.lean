module

public import NLA.IV04.PaperRationalParserDefinitions
public import NLA.IV04.PaperNaturalParserSemantics
public import NLA.IV04.PaperFractionWordSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem natural_parser_flag_boolean (input : List Bool) :
    Complexity.pairFst (encodedNaturalParser input)=[true] ∨
      Complexity.pairFst (encodedNaturalParser input)=[false] := by
  rw [natural_parser_flag,natural_parse_flag_stages]
  split_ifs <;> simp

theorem rational_parser_flag_stages (input : List Bool) :
    rationalParserFlag input=
      if input=[] then [false]
      else if Complexity.pairFst (rationalParserFirst input)=[true] ∧
        Complexity.pairFst (rationalParserSecond input)=[true] then [true] else [false] := by
  cases input with
  | nil => simp [rationalParserFlag,Complexity.nonemptyFlag,Complexity.caseBit,Complexity.andBit,Complexity.caseBit₀]
  | cons b bits =>
    have hf := natural_parser_flag_boolean (b :: bits).tail
    have hs := natural_parser_flag_boolean
      (Complexity.pairSnd (Complexity.pairSnd (rationalParserFirst (b :: bits))))
    change Complexity.pairFst (rationalParserFirst (b :: bits))=[true] ∨
      Complexity.pairFst (rationalParserFirst (b :: bits))=[false] at hf
    change Complexity.pairFst (rationalParserSecond (b :: bits))=[true] ∨
      Complexity.pairFst (rationalParserSecond (b :: bits))=[false] at hs
    rcases hf with hf | hf <;> rcases hs with hs | hs <;>
      simp [rationalParserFlag,hf,hs,Complexity.nonemptyFlag,Complexity.caseBit,
        Complexity.andBit,Complexity.caseBit₀]

theorem rational_parser_flag (input : List Bool) :
    Complexity.pairFst (encodedRationalParser input)=rationalParserFlag input := by
  simp [encodedRationalParser]

theorem rational_parser_fraction (input : List Bool) :
    Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))=rationalParserFraction input := by
  simp [encodedRationalParser]

theorem rational_parser_tail (input : List Bool) :
    Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))=
      Complexity.pairSnd (Complexity.pairSnd (rationalParserSecond input)) := by
  simp [encodedRationalParser]

theorem rational_parser_denominator_positive (input : List Bool) :
    0 < wordValue (Complexity.pairSnd (rationalParserFraction input)) :=
  normalize_fraction_denominator_positive _

theorem rational_parser_fraction_value (input : List Bool) :
    fractionWordValue (rationalParserFraction input)=
      ((if firstBit input then
          -(wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))) : ℤ)
        else (wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))) : ℤ)) : ℚ)/
      (wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))) : ℚ) := by
  unfold rationalParserFraction
  rw [normalize_fraction_word_value]
  simp only [fractionWordValue,Complexity.pairFst_pair,Complexity.pairSnd_pair,head_flag,
    signed_word_pack_flag_value]
  split_ifs <;> simp only [Int.cast_neg]

theorem rational_parser_bind_identity (b : Bool) (first : List Bool)
    (parse : List Bool → List Bool) :
    (if (if Complexity.pairFst first=[true] ∧
        Complexity.pairFst (parse (Complexity.pairSnd (Complexity.pairSnd first)))=[true]
      then [true] else [false])=[true] then
      some ((if b then -((wordValue (Complexity.pairFst (Complexity.pairSnd first)) : ℤ) : ℚ)
        else ((wordValue (Complexity.pairFst (Complexity.pairSnd first)) : ℤ) : ℚ))/
        (wordValue (Complexity.pairFst (Complexity.pairSnd
          (parse (Complexity.pairSnd (Complexity.pairSnd first))))) : ℚ),
        Complexity.pairSnd (Complexity.pairSnd (parse (Complexity.pairSnd (Complexity.pairSnd first)))))
      else none)=
    (Option.bind (if Complexity.pairFst first=[true] then
        some (wordValue (Complexity.pairFst (Complexity.pairSnd first)),
          Complexity.pairSnd (Complexity.pairSnd first)) else none)
      (fun x => Option.bind (if Complexity.pairFst (parse x.2)=[true] then
        some (wordValue (Complexity.pairFst (Complexity.pairSnd (parse x.2))),
          Complexity.pairSnd (Complexity.pairSnd (parse x.2))) else none)
        (fun y =>
          let signed : ℤ := if b then -(x.1 : ℤ) else (x.1 : ℤ)
          some ((signed : ℚ)/(y.1 : ℚ),y.2)))) := by
  by_cases hf : Complexity.pairFst first=[true]
  · by_cases hs : Complexity.pairFst (parse (Complexity.pairSnd (Complexity.pairSnd first)))=[true]
    · cases b <;> simp [hf,hs]
    · simp [hf,hs]
  · simp [hf]

theorem rational_parser_exact (input : List Bool) :
    (if Complexity.pairFst (encodedRationalParser input)=[true] then
      some (fractionWordValue (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input)))
      else none)=IV04.Paper.readRational input := by
  rw [rational_parser_flag,rational_parser_fraction,rational_parser_tail,rational_parser_flag_stages,
    rational_parser_fraction_value]
  cases input with
  | nil => simp [IV04.Paper.readRational]
  | cons b bits =>
    simp only [List.cons_ne_nil,ite_false,rationalParserFirst,rationalParserSecond,
      List.tail_cons,firstBit,List.headD_cons]
    simp only [IV04.Paper.readRational,←natural_parser_exact]
    exact rational_parser_bind_identity b (encodedNaturalParser bits) encodedNaturalParser

#print axioms rational_parser_exact
end IV04.Paper.Computational
