module

public import NLA.IV04.PaperEncodingSize
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Matrix
namespace IV04.Paper

theorem verified_sum_lt_two_pow_sum_size {ι : Type*} (S : Finset ι) (w : ι → ℕ) :
    (∑ i ∈ S, w i) < 2^(∑ i ∈ S, (w i).size) := by
  exact sum_lt_two_pow_sum_size S w

namespace IntegerPartition
theorem verified_total_lt_binary_bound (P : IntegerPartition) :
    P.total < 2^P.inputBits := by
  exact total_lt_binary_bound P
end IntegerPartition


namespace IntegerPartition
theorem verified_dimension_le_input_bits (P : IntegerPartition) : P.m ≤ P.inputBits := by
  exact dimension_le_input_bits P
end IntegerPartition


namespace IntegerPartition
theorem verified_squared_scale_identity (P : IntegerPartition) :
    P.squaredScale = 100*P.total^4 := by
  exact squared_scale_identity P
end IntegerPartition


namespace IntegerPartition
theorem verified_squared_weight_lt_scale (P : IntegerPartition) (i : Fin P.m) :
    (P.weight i)^2 < P.squaredScale := by
  exact squared_weight_lt_scale P i
end IntegerPartition


namespace IntegerPartition
theorem verified_entry_magnitude_lt_binary_bound (P : IntegerPartition) :
    P.entryMagnitudeBound < 2^P.entryBitBound := by
  exact entry_magnitude_lt_binary_bound P
end IntegerPartition


namespace IntegerPartition
theorem verified_magnitude_size_bound (P : IntegerPartition) (n : ℕ)
    (hn : n ≤ P.entryMagnitudeBound) : n.size ≤ P.entryBitBound := by
  exact magnitude_size_bound P n hn
end IntegerPartition


namespace IntegerPartition
theorem verified_rotation_denominator_bound (P : IntegerPartition) (i : Fin P.m) :
    P.squaredScale+(P.weight i)^2 ≤ P.entryMagnitudeBound := by
  exact rotation_denominator_bound P i
end IntegerPartition


namespace IntegerPartition
theorem verified_positive_companion_denominator (P : IntegerPartition) (i : Fin P.m) :
    0 < P.squaredScale-(P.weight i)^2 := by
  exact positive_companion_denominator P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_denominator_bound (P : IntegerPartition) (i : Fin P.m) :
    P.squaredScale-(P.weight i)^2 ≤ P.entryMagnitudeBound := by
  exact companion_denominator_bound P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sine_numerator_bound (P : IntegerPartition) (i : Fin P.m) :
    2*P.weight i*P.denominatorScale ≤ P.entryMagnitudeBound := by
  exact sine_numerator_bound P i
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_denominator_bound (P : IntegerPartition) :
    2*P.squaredScale = P.entryMagnitudeBound := by
  exact threshold_denominator_bound P
end IntegerPartition


namespace IntegerPartition
theorem verified_rotation_denominator_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.squaredScale+(P.weight i)^2).size ≤ P.entryBitBound := by
  exact rotation_denominator_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_denominator_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.squaredScale-(P.weight i)^2).size ≤ P.entryBitBound := by
  exact companion_denominator_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sine_numerator_bits (P : IntegerPartition) (i : Fin P.m) :
    (2*P.weight i*P.denominatorScale).size ≤ P.entryBitBound := by
  exact sine_numerator_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_denominator_bits (P : IntegerPartition) :
    (2*P.squaredScale).size ≤ P.entryBitBound := by
  exact threshold_denominator_bits P
end IntegerPartition


theorem verified_reduced_fraction_payload (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((a : ℚ)/(b : ℚ)).num.natAbs ≤ a.natAbs ∧
    ((a : ℚ)/(b : ℚ)).den ≤ b := by
  exact reduced_fraction_payload a b hb

namespace IntegerPartition
theorem verified_cosine_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.c i = ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2)/
      ((P.squaredScale : ℚ)+(P.weight i : ℚ)^2) := by
  exact cosine_scaled_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sine_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.s i = (2*(P.weight i : ℚ)*P.denominatorScale)/
      ((P.squaredScale : ℚ)+(P.weight i : ℚ)^2) := by
  exact sine_scaled_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_diagonal_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    -P.s i/P.c i = -(2*(P.weight i : ℚ)*P.denominatorScale)/
      ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2) := by
  exact companion_diagonal_scaled_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_beta_scaled_fraction (P : IntegerPartition) (i : Fin P.m) :
    -1/P.c i = -((P.squaredScale : ℚ)+(P.weight i : ℚ)^2)/
      ((P.squaredScale : ℚ)-(P.weight i : ℚ)^2) := by
  exact companion_beta_scaled_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_scaled_fraction (P : IntegerPartition) :
    P.threshold = (2*(P.squaredScale : ℚ)-1)/(2*(P.squaredScale : ℚ)) := by
  exact threshold_scaled_fraction P
end IntegerPartition


namespace IntegerPartition
theorem verified_fraction_bits (P : IntegerPartition) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (ha : a.natAbs ≤ P.entryMagnitudeBound) (hbb : b ≤ P.entryMagnitudeBound) :
    (((a : ℚ)/(b : ℚ)).num.natAbs).size ≤ P.entryBitBound ∧
      (((a : ℚ)/(b : ℚ)).den).size ≤ P.entryBitBound := by
  exact fraction_bits P a b hb ha hbb
end IntegerPartition


namespace IntegerPartition
theorem verified_cosine_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.c i = ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ)/
      ((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ) := by
  exact cosine_nat_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sine_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.s i = ((2*P.weight i*P.denominatorScale : ℕ) : ℚ)/
      ((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ) := by
  exact sine_nat_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_diagonal_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    -P.s i/P.c i = -((2*P.weight i*P.denominatorScale : ℕ) : ℚ)/
      ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ) := by
  exact companion_diagonal_nat_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_beta_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    -1/P.c i = -((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ)/
      ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ) := by
  exact companion_beta_nat_fraction P i
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_nat_fraction (P : IntegerPartition) :
    P.threshold = ((2*P.squaredScale-1 : ℕ) : ℚ)/((2*P.squaredScale : ℕ) : ℚ) := by
  exact threshold_nat_fraction P
end IntegerPartition


namespace IntegerPartition
theorem verified_cosine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.c i).num.natAbs.size ≤ P.entryBitBound ∧ (P.c i).den.size ≤ P.entryBitBound := by
  exact cosine_payload_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_sine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.s i).num.natAbs.size ≤ P.entryBitBound ∧ (P.s i).den.size ≤ P.entryBitBound := by
  exact sine_payload_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_diagonal_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-P.s i/P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.s i/P.c i).den.size ≤ P.entryBitBound := by
  exact companion_diagonal_payload_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_companion_beta_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-1/P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-1/P.c i).den.size ≤ P.entryBitBound := by
  exact companion_beta_payload_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_payload_bits (P : IntegerPartition) :
    P.threshold.num.natAbs.size ≤ P.entryBitBound ∧
      P.threshold.den.size ≤ P.entryBitBound := by
  exact threshold_payload_bits P
end IntegerPartition


namespace IntegerPartition
theorem verified_constant_payload_bits (P : IntegerPartition) (r : ℚ)
    (hr : r=0 ∨ r=1 ∨ r= -1) :
    r.num.natAbs.size ≤ P.entryBitBound ∧ r.den.size ≤ P.entryBitBound := by
  exact constant_payload_bits P r hr
end IntegerPartition


namespace IntegerPartition
theorem verified_negative_cosine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.c i).den.size ≤ P.entryBitBound := by
  exact negative_cosine_payload_bits P i
end IntegerPartition


namespace IntegerPartition
theorem verified_extended_sine_payload_bits (P : IntegerPartition) (j : ℕ) :
    (P.sAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.sAt j).den.size ≤ P.entryBitBound := by
  exact extended_sine_payload_bits P j
end IntegerPartition


namespace IntegerPartition
theorem verified_extended_diagonal_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-P.sAt j/P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.sAt j/P.cAt j).den.size ≤ P.entryBitBound := by
  exact extended_diagonal_payload_bits P j
end IntegerPartition


namespace IntegerPartition
theorem verified_extended_negative_cosine_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.cAt j).den.size ≤ P.entryBitBound := by
  exact extended_negative_cosine_payload_bits P j
end IntegerPartition


namespace IntegerPartition
theorem verified_extended_beta_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-1/P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-1/P.cAt j).den.size ≤ P.entryBitBound := by
  exact extended_beta_payload_bits P j
end IntegerPartition


namespace IntegerPartition
theorem verified_layer_diagonal_payload_bits (P : IntegerPartition) (j : ℕ) :
    (P.layerDiagonal j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.layerDiagonal j).den.size ≤ P.entryBitBound := by
  exact layer_diagonal_payload_bits P j
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_lower_payload_bits (P : IntegerPartition) (i j : Fin P.layerCount) :
    (P.rationalLower i j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.rationalLower i j).den.size ≤ P.entryBitBound := by
  exact matrix_lower_payload_bits P i j
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_upper_payload_bits (P : IntegerPartition) (i j : Fin P.layerCount) :
    (P.rationalUpper i j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.rationalUpper i j).den.size ≤ P.entryBitBound := by
  exact matrix_upper_payload_bits P i j
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_dimension_bound (P : IntegerPartition) :
    P.layerCount ≤ 4*P.inputBits := by
  exact matrix_dimension_bound P
end IntegerPartition


theorem verified_bits_foldr (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  exact bits_foldr n

theorem verified_read_unary_header (n : ℕ) (tail : List Bool) :
    readUnary (List.replicate n true ++ false :: tail) = some (n,tail) := by
  exact read_unary_header n tail

theorem verified_read_natural_code (n : ℕ) (tail : List Bool) :
    readNatural (naturalCode n ++ tail) = some (n,tail) := by
  exact read_natural_code n tail

theorem verified_natural_code_injective : Function.Injective naturalCode := by
  exact natural_code_injective

theorem verified_natural_code_length (n : ℕ) : (naturalCode n).length = 2*n.size+1 := by
  exact natural_code_length n

theorem verified_signed_magnitude (z : ℤ) :
    (if z<0 then -(z.natAbs : ℤ) else (z.natAbs : ℤ)) = z := by
  exact signed_magnitude z

theorem verified_read_rational_code (q : ℚ) (tail : List Bool) :
    readRational (rationalCode q ++ tail) = some (q,tail) := by
  exact read_rational_code q tail

theorem verified_rational_code_injective : Function.Injective rationalCode := by
  exact rational_code_injective

theorem verified_rational_code_length (q : ℚ) :
    (rationalCode q).length = 2*q.num.natAbs.size+2*q.den.size+3 := by
  exact rational_code_length q

namespace IntegerPartition
theorem verified_rational_code_length_bound (P : IntegerPartition) (q : ℚ)
    (hq : q.num.natAbs.size ≤ P.entryBitBound ∧ q.den.size ≤ P.entryBitBound) :
    (rationalCode q).length ≤ 4*P.entryBitBound+3 := by
  exact rational_code_length_bound P q hq
end IntegerPartition


namespace IntegerPartition
theorem verified_threshold_code_length_bound (P : IntegerPartition) :
    (rationalCode P.threshold).length ≤ 4*P.entryBitBound+3 := by
  exact threshold_code_length_bound P
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_entry_code_length_bound (P : IntegerPartition) (i j : Fin P.layerCount) :
    (rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j)).length ≤
      2*(4*P.entryBitBound+3) := by
  exact matrix_entry_code_length_bound P i j
end IntegerPartition


theorem verified_flatMap_length_bound {α β : Type*} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ B) : (xs.flatMap f).length ≤ xs.length*B := by
  exact flatMap_length_bound xs f B h

namespace IntegerPartition
theorem verified_matrix_rows_code_bound (P : IntegerPartition) :
    ((List.finRange P.layerCount).flatMap (fun i =>
      (List.finRange P.layerCount).flatMap (fun j =>
        rationalCode (P.rationalLower i j) ++ rationalCode (P.rationalUpper i j)))).length ≤
      P.layerCount^2*(2*(4*P.entryBitBound+3)) := by
  exact matrix_rows_code_bound P
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_box_code_size (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*P.layerCount^2+1)*(4*P.entryBitBound+3)+2*P.layerCount.size+1 := by
  exact matrix_box_code_size P
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_box_code_polynomial_size (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*(4*P.inputBits)^2+1)*(16*P.inputBits+35)+8*P.inputBits+1 := by
  exact matrix_box_code_polynomial_size P
end IntegerPartition


#print axioms IV04.Paper.verified_sum_lt_two_pow_sum_size
#print axioms IV04.Paper.IntegerPartition.verified_total_lt_binary_bound
#print axioms IV04.Paper.IntegerPartition.verified_dimension_le_input_bits
#print axioms IV04.Paper.IntegerPartition.verified_squared_scale_identity
#print axioms IV04.Paper.IntegerPartition.verified_squared_weight_lt_scale
#print axioms IV04.Paper.IntegerPartition.verified_entry_magnitude_lt_binary_bound
#print axioms IV04.Paper.IntegerPartition.verified_magnitude_size_bound
#print axioms IV04.Paper.IntegerPartition.verified_rotation_denominator_bound
#print axioms IV04.Paper.IntegerPartition.verified_positive_companion_denominator
#print axioms IV04.Paper.IntegerPartition.verified_companion_denominator_bound
#print axioms IV04.Paper.IntegerPartition.verified_sine_numerator_bound
#print axioms IV04.Paper.IntegerPartition.verified_threshold_denominator_bound
#print axioms IV04.Paper.IntegerPartition.verified_rotation_denominator_bits
#print axioms IV04.Paper.IntegerPartition.verified_companion_denominator_bits
#print axioms IV04.Paper.IntegerPartition.verified_sine_numerator_bits
#print axioms IV04.Paper.IntegerPartition.verified_threshold_denominator_bits
#print axioms IV04.Paper.verified_reduced_fraction_payload
#print axioms IV04.Paper.IntegerPartition.verified_cosine_scaled_fraction
#print axioms IV04.Paper.IntegerPartition.verified_sine_scaled_fraction
#print axioms IV04.Paper.IntegerPartition.verified_companion_diagonal_scaled_fraction
#print axioms IV04.Paper.IntegerPartition.verified_companion_beta_scaled_fraction
#print axioms IV04.Paper.IntegerPartition.verified_threshold_scaled_fraction
#print axioms IV04.Paper.IntegerPartition.verified_fraction_bits
#print axioms IV04.Paper.IntegerPartition.verified_cosine_nat_fraction
#print axioms IV04.Paper.IntegerPartition.verified_sine_nat_fraction
#print axioms IV04.Paper.IntegerPartition.verified_companion_diagonal_nat_fraction
#print axioms IV04.Paper.IntegerPartition.verified_companion_beta_nat_fraction
#print axioms IV04.Paper.IntegerPartition.verified_threshold_nat_fraction
#print axioms IV04.Paper.IntegerPartition.verified_cosine_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_sine_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_companion_diagonal_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_companion_beta_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_threshold_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_constant_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_negative_cosine_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_extended_sine_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_extended_diagonal_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_extended_negative_cosine_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_extended_beta_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_layer_diagonal_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_matrix_lower_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_matrix_upper_payload_bits
#print axioms IV04.Paper.IntegerPartition.verified_matrix_dimension_bound
#print axioms IV04.Paper.verified_bits_foldr
#print axioms IV04.Paper.verified_read_unary_header
#print axioms IV04.Paper.verified_read_natural_code
#print axioms IV04.Paper.verified_natural_code_injective
#print axioms IV04.Paper.verified_natural_code_length
#print axioms IV04.Paper.verified_signed_magnitude
#print axioms IV04.Paper.verified_read_rational_code
#print axioms IV04.Paper.verified_rational_code_injective
#print axioms IV04.Paper.verified_rational_code_length
#print axioms IV04.Paper.IntegerPartition.verified_rational_code_length_bound
#print axioms IV04.Paper.IntegerPartition.verified_threshold_code_length_bound
#print axioms IV04.Paper.IntegerPartition.verified_matrix_entry_code_length_bound
#print axioms IV04.Paper.verified_flatMap_length_bound
#print axioms IV04.Paper.IntegerPartition.verified_matrix_rows_code_bound
#print axioms IV04.Paper.IntegerPartition.verified_matrix_box_code_size
#print axioms IV04.Paper.IntegerPartition.verified_matrix_box_code_polynomial_size
end IV04.Paper
