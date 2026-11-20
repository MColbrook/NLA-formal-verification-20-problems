module

public import NLA.IV04.PaperWordSubtractionDefinitions
public import NLA.IV04.PaperWordComparisonSemantics
public import NLA.IV04.PaperWordAdderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem bit_value_le_one (b : Bool) : bitValue b ≤ 1 := by cases b <;> simp [bitValue]

theorem word_value_lt_pow_length (bits : List Bool) : wordValue bits < 2^bits.length := by
  induction bits with
  | nil => simp [wordValue]
  | cons b bits ih =>
    have hb := bit_value_le_one b
    simp only [wordValue,List.length_cons,pow_succ]
    nlinarith

theorem word_value_append (left right : List Bool) :
    wordValue (left++right)=wordValue left+2^left.length*wordValue right := by
  induction left with
  | nil => simp [wordValue]
  | cons b bits ih => simp only [List.cons_append,wordValue,List.length_cons,pow_succ,ih]; ring

theorem word_value_zeros (k : ℕ) : wordValue (List.replicate k false)=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,wordValue,bitValue,ih]

theorem word_value_pad (ruler bits : List Bool) (h : bits.length ≤ ruler.length) :
    wordValue (Complexity.padTo ruler bits)=wordValue bits := by
  rw [Complexity.padTo_eq_append ruler bits h,word_value_append,word_value_zeros]
  simp

theorem word_value_complement (bits : List Bool) :
    wordValue (bits.map Bool.not)+wordValue bits+1=2^bits.length := by
  induction bits with
  | nil => simp [wordValue]
  | cons b bits ih =>
    cases b <;> simp only [List.map_cons,wordValue,bitValue,Bool.not_false,Bool.not_true,
      Bool.false_eq_true,ite_false,ite_true,List.length_cons,pow_succ] <;> nlinarith

theorem word_value_split (bits : List Bool) (k : ℕ) :
    wordValue bits=wordValue (bits.take k)+2^k*wordValue (bits.drop k) := by
  induction k generalizing bits with
  | zero => simp [wordValue]
  | succ k ih =>
    cases bits with
    | nil => simp [wordValue]
    | cons b bits =>
      simp only [List.take_succ_cons,List.drop_succ_cons,wordValue,pow_succ]
      rw [ih bits]
      ring

theorem word_value_take_bound (bits : List Bool) (k : ℕ) :
    wordValue (bits.take k) < 2^k := by
  induction k generalizing bits with
  | zero => simp [wordValue]
  | succ k ih =>
    cases bits with
    | nil => simp [wordValue]
    | cons b bits =>
      have ht := ih bits
      have hb := bit_value_le_one b
      simp only [List.take_succ_cons,wordValue,pow_succ]
      nlinarith

theorem word_value_take_mod (bits : List Bool) (k : ℕ) :
    wordValue (bits.take k)=wordValue bits % 2^k := by
  have h := word_value_take_bound bits k
  conv_rhs => rw [word_value_split bits k]
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_of_lt h]

theorem raw_word_difference_value (left right : List Bool)
    (h : wordValue right ≤ wordValue left) :
    wordValue (rawWordDifference left right)=wordValue left-wordValue right := by
  let ruler := false :: (left++right)
  have hr : right.length ≤ ruler.length := by simp [ruler]; omega
  have hc := word_value_complement (Complexity.padTo ruler right)
  rw [word_value_pad ruler right hr,Complexity.padTo_length] at hc
  have ht := word_value_take_bound left ruler.length
  have he : left.take ruler.length=left := List.take_of_length_le (by simp [ruler]; omega)
  rw [he] at ht
  have hd : wordValue left-wordValue right < 2^ruler.length := by omega
  have hs : wordValue (polynomialWordAdd left
      (polynomialWordAdd [true] ((Complexity.padTo ruler right).map Bool.not)))=
      (wordValue left-wordValue right)+2^ruler.length := by
    rw [polynomial_word_add_value,polynomial_word_add_value]
    simp only [wordValue,bitValue,ite_true]
    omega
  change wordValue ((polynomialWordAdd left
    (polynomialWordAdd [true] ((Complexity.padTo ruler right).map Bool.not))).take ruler.length)=_
  rw [word_value_take_mod,hs]
  simp [Nat.add_mod,Nat.mod_eq_of_lt hd]

theorem polynomial_word_sub_value (left right : List Bool) :
    wordValue (polynomialWordSub left right)=wordValue left-wordValue right := by
  unfold polynomialWordSub
  rw [polynomial_word_le_value]
  by_cases h : wordValue right ≤ wordValue left
  · simpa [h,Complexity.caseBit₀] using raw_word_difference_value left right h
  · simp [h,Complexity.caseBit₀,wordValue,Nat.sub_eq_zero_of_le (by omega : wordValue left ≤ wordValue right)]

theorem raw_word_difference_length (left right : List Bool) :
    (rawWordDifference left right).length ≤ left.length+right.length+1 := by
  simp only [rawWordDifference,List.length_take,List.length_cons,List.length_append]
  omega

theorem polynomial_word_sub_length (left right : List Bool) :
    (polynomialWordSub left right).length ≤ left.length+right.length+1 := by
  unfold polynomialWordSub
  rw [polynomial_word_le_value]
  by_cases h : wordValue right ≤ wordValue left
  · simpa [h,Complexity.caseBit₀] using raw_word_difference_length left right
  · simp [h,Complexity.caseBit₀]

#print axioms polynomial_word_sub_value
end IV04.Paper.Computational
