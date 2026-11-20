module

public import NLA.IV04.PaperEncodingDefinitions
public import NLA.IV04.PaperMatrixBits
public import Mathlib.Data.List.FinRange

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper

theorem bits_foldr (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih => simp [Nat.bits_append_bit n b hn,ih]

theorem read_unary_header (n : ℕ) (tail : List Bool) :
    readUnary (List.replicate n true ++ false :: tail) = some (n,tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,readUnary,ih]

theorem read_natural_code (n : ℕ) (tail : List Bool) :
    readNatural (naturalCode n ++ tail) = some (n,tail) := by
  have he : naturalCode n ++ tail =
      List.replicate n.bits.length true ++ false :: (n.bits ++ tail) := by
    simp [naturalCode,List.append_assoc]
  rw [he]
  simp [readNatural,read_unary_header,bits_foldr]

theorem natural_code_injective : Function.Injective naturalCode := by
  intro a b h
  have ha := read_natural_code a []
  have hb := read_natural_code b []
  rw [h] at ha
  rw [hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

theorem natural_code_length (n : ℕ) : (naturalCode n).length = 2*n.size+1 := by
  simp [naturalCode,Nat.size_eq_bits_len]
  omega

theorem signed_magnitude (z : ℤ) :
    (if z<0 then -(z.natAbs : ℤ) else (z.natAbs : ℤ)) = z := by
  split_ifs with h
  · rw [Int.natCast_natAbs]
    simp [abs_of_neg h]
  · rw [Int.natCast_natAbs]
    exact abs_of_nonneg (by omega)

theorem read_rational_code (q : ℚ) (tail : List Bool) :
    readRational (rationalCode q ++ tail) = some (q,tail) := by
  have he : (if decide (q.num<0) then -(q.num.natAbs : ℤ) else (q.num.natAbs : ℤ)) = q.num := by
    simpa using signed_magnitude q.num
  simp only [readRational,rationalCode,List.cons_append,List.append_assoc,
    read_natural_code,bind,Option.bind_some,Option.pure_def]
  rw [he,Rat.num_div_den]

theorem rational_code_injective : Function.Injective rationalCode := by
  intro a b h
  have ha := read_rational_code a []
  have hb := read_rational_code b []
  rw [h] at ha
  rw [hb] at ha
  exact (congrArg Prod.fst (Option.some.inj ha)).symm

theorem rational_code_length (q : ℚ) :
    (rationalCode q).length = 2*q.num.natAbs.size+2*q.den.size+3 := by
  simp [rationalCode,natural_code_length]
  omega

namespace IntegerPartition

theorem rational_code_length_bound (P : IntegerPartition) (q : ℚ)
    (hq : q.num.natAbs.size ≤ P.entryBitBound ∧ q.den.size ≤ P.entryBitBound) :
    (rationalCode q).length ≤ 4*P.entryBitBound+3 := by
  rw [rational_code_length]
  omega

theorem threshold_code_length_bound (P : IntegerPartition) :
    (rationalCode P.threshold).length ≤ 4*P.entryBitBound+3 :=
  rational_code_length_bound P _ (threshold_payload_bits P)

theorem matrix_entry_code_length_bound (P : IntegerPartition) (i j : Fin P.layerCount) :
    (rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j)).length ≤
      2*(4*P.entryBitBound+3) := by
  have hl := rational_code_length_bound P _ (matrix_lower_payload_bits P i j)
  have hu := rational_code_length_bound P _ (matrix_upper_payload_bits P i j)
  rw [List.length_append]
  omega

end IntegerPartition
end IV04.Paper
