module

public import NLA.IV04.PaperRationalBits
public import NLA.IV04.PaperCubeDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.IntegerPartition

theorem constant_payload_bits (P : IntegerPartition) (r : ℚ)
    (hr : r=0 ∨ r=1 ∨ r= -1) :
    r.num.natAbs.size ≤ P.entryBitBound ∧ r.den.size ≤ P.entryBitBound := by
  rcases hr with rfl | rfl | rfl <;> norm_num [entryBitBound]

theorem negative_cosine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.c i).den.size ≤ P.entryBitBound := by
  simpa only [Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den]
    using cosine_payload_bits P i

theorem extended_sine_payload_bits (P : IntegerPartition) (j : ℕ) :
    (P.sAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.sAt j).den.size ≤ P.entryBitBound := by
  by_cases h : j<P.m
  · simpa only [sAt,dif_pos h] using sine_payload_bits P ⟨j,h⟩
  · simpa only [sAt,dif_neg h] using constant_payload_bits P 0 (Or.inl rfl)

theorem extended_diagonal_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-P.sAt j/P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.sAt j/P.cAt j).den.size ≤ P.entryBitBound := by
  by_cases h : j<P.m
  · simpa only [sAt,cAt,dif_pos h] using companion_diagonal_payload_bits P ⟨j,h⟩
  · simpa [sAt,cAt,h] using constant_payload_bits P 0 (Or.inl rfl)

theorem extended_negative_cosine_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.cAt j).den.size ≤ P.entryBitBound := by
  by_cases h : j<P.m
  · simpa only [cAt,dif_pos h] using negative_cosine_payload_bits P ⟨j,h⟩
  · simpa only [cAt,dif_neg h] using constant_payload_bits P (-1) (Or.inr (Or.inr rfl))

theorem extended_beta_payload_bits (P : IntegerPartition) (j : ℕ) :
    (-1/P.cAt j).num.natAbs.size ≤ P.entryBitBound ∧
      (-1/P.cAt j).den.size ≤ P.entryBitBound := by
  by_cases h : j<P.m
  · simpa only [cAt,dif_pos h] using companion_beta_payload_bits P ⟨j,h⟩
  · simpa [cAt,h] using constant_payload_bits P (-1) (Or.inr (Or.inr rfl))

theorem layer_diagonal_payload_bits (P : IntegerPartition) (j : ℕ) :
    (P.layerDiagonal j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.layerDiagonal j).den.size ≤ P.entryBitBound := by
  dsimp [layerDiagonal]
  split_ifs
  · exact extended_sine_payload_bits P (j/4)
  · exact extended_diagonal_payload_bits P (j/4)
  · exact constant_payload_bits P 0 (Or.inl rfl)

theorem matrix_lower_payload_bits (P : IntegerPartition) (i j : Fin P.layerCount) :
    (P.rationalLower i j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.rationalLower i j).den.size ≤ P.entryBitBound := by
  dsimp [rationalLower]
  split_ifs
  · exact layer_diagonal_payload_bits P i.val
  · exact constant_payload_bits P 1 (Or.inr (Or.inl rfl))
  · exact extended_negative_cosine_payload_bits P (i.val/4)
  · exact extended_beta_payload_bits P (i.val/4)
  · exact constant_payload_bits P (-1) (Or.inr (Or.inr rfl))
  · exact constant_payload_bits P 0 (Or.inl rfl)

theorem matrix_upper_payload_bits (P : IntegerPartition) (i j : Fin P.layerCount) :
    (P.rationalUpper i j).num.natAbs.size ≤ P.entryBitBound ∧
      (P.rationalUpper i j).den.size ≤ P.entryBitBound := by
  dsimp [rationalUpper]
  split_ifs
  · exact constant_payload_bits P 1 (Or.inr (Or.inl rfl))
  · exact matrix_lower_payload_bits P i j

theorem matrix_dimension_bound (P : IntegerPartition) :
    P.layerCount ≤ 4*P.inputBits := by
  have h := dimension_le_input_bits P
  dsimp [layerCount]
  omega

end IV04.Paper.IntegerPartition
