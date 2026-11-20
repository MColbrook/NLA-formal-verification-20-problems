module

public import NLA.PF02.GlobalOrientation.Polynomial
public import NLA.PF02.PaperSymmetricRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

theorem trace_rank_le_coordinate_rank {n : ℕ}
    (C B : SymIndex n → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ p, (C p).transpose = C p) :
    Matrix.rank ((fun p q => trace (C p * B q)) : Matrix (SymIndex n) (SymIndex n) ℝ) ≤
      (coordinateRows C).rank := by
  let V : Matrix (SymIndex n) (SymIndex n) ℝ := fun a j => trace (symmetricUnit n a * B j)
  have heq : (fun p q => trace (C p * B q) : Matrix (SymIndex n) (SymIndex n) ℝ) =
      coordinateRows C * V := by
    ext p q
    change trace (C p * B q) = ∑ a, symmetricCoordinates (C p) a * trace (symmetricUnit n a * B q)
    conv_lhs => rw [← matrix_coordinates (C p) (hC p), symmetricMatrix_sum]
    simp [Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
  rw [heq]
  exact Matrix.rank_mul_le_left _ _

theorem coordinate_det_ne_zero_of_full_trace_rank {n : ℕ}
    (C B : SymIndex n → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ p, (C p).transpose = C p)
    (hRank : Matrix.rank ((fun p q => trace (C p * B q)) : Matrix (SymIndex n) (SymIndex n) ℝ) =
      Fintype.card (SymIndex n)) : (coordinateRows C).det ≠ 0 := by
  classical
  have hl := trace_rank_le_coordinate_rank C B hC
  have hu := Matrix.rank_le_card_width (coordinateRows C)
  have hr : (coordinateRows C).rank = Fintype.card (SymIndex n) := by rw [hRank] at hl; omega
  have hi : LinearIndependent ℝ (coordinateRows C).row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row, hr]
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hi)

theorem orthogonal_lift_orientation_product_pos {k : ℕ}
    (T : Matrix (Fin k) (Fin 3) ℝ) (hT : T.transpose * T = 1)
    (C : SymIndex 3 → Matrix (Fin 3) (Fin 3) ℝ) (hC : ∀ p, (C p).transpose = C p)
    (hD : (coordinateRows C).det ≠ 0)
    (O : Matrix (Fin k) (Fin k) ℝ) (hO : O * O.transpose = 1) :
    0 < orientationPolynomial (fun p => T * C p * T.transpose) *
      orientationPolynomial (fun p => O.transpose * (T * C p * T.transpose) * O) := by
  let T' := O.transpose * T
  have hT' : T'.transpose * T' = 1 := by
    simp only [T', Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      T.transpose * O * (O.transpose * T) = T.transpose * (O * O.transpose) * T := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hO, Matrix.mul_one, hT]
  have heq : (fun p => O.transpose * (T * C p * T.transpose) * O) =
      (fun p => T' * C p * T'.transpose) := by
    funext p
    simp only [T', Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [heq, orientation_polynomial_lift T C hC, orientation_polynomial_lift T' C hC]
  have hp := mul_pos (sq_pos_of_ne_zero hD) (mul_pos (frame_weight_pos T hT) (frame_weight_pos T' hT'))
  nlinarith [hp]

#print axioms trace_rank_le_coordinate_rank
#print axioms coordinate_det_ne_zero_of_full_trace_rank
#print axioms orthogonal_lift_orientation_product_pos
end Reference.PF02GlobalOrientation
