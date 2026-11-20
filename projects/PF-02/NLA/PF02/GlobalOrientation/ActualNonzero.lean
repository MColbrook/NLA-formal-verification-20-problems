module

public import NLA.PF02.GlobalOrientation.ActualDefinitions
public import NLA.PF02.GlobalOrientation.IntrinsicNonzero
public import NLA.PF02.BlockSupportRecovery.Recovery

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02BlockSupportRecovery
open Reference.PF02IntrinsicSupport Reference.PF02Support Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem actual_leading_frame {r : ℕ} (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) :
    ∃ T : Matrix (Fin (3+r)) (Fin 3) ℝ, T.transpose * T = 1 ∧
      LinearMap.range (Matrix.toEuclideanLin T) = kernel (trailingSum F.val.2) := by
  have hd := (actual_recovered_support_dimensions F).2.2
  have hf := exists_orthonormal_frame (kernel (trailingSum F.val.2))
  rw [hd] at hf
  exact hf

theorem actual_leading_coordinate_det_ne_zero {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r))
    (T : Matrix (Fin (3+r)) (Fin 3) ℝ) (hT : T.transpose * T = 1)
    (hRange : LinearMap.range (Matrix.toEuclideanLin T) = kernel (trailingSum F.val.2)) :
    (coordinateRows (fun p => T.transpose * leadingRows F.val.1 p * T)).det ≠ 0 := by
  let C := fun p => T.transpose * leadingRows F.val.1 p * T
  let B := fun p => T.transpose * leadingRows F.val.2 p * T
  have hA : ∀ p, (leadingRows F.val.1 p).transpose = leadingRows F.val.1 p := by
    intro p
    ext a b
    simpa only [leadingRows, blockRows, Matrix.transpose_apply, star_trivial] using
      (F.property.1 (Fintype.equivFin (BlockIndex r) (Sum.inl p))).isHermitian.apply a b
  have hC : ∀ p, (C p).transpose = C p := by
    intro p
    simp only [C, Matrix.transpose_mul, Matrix.transpose_transpose, hA p, Matrix.mul_assoc]
  have hs : ∀ p, image (leadingRows F.val.1 p) ≤ LinearMap.range (Matrix.toEuclideanLin T) := by
    intro p
    rw [hRange]
    exact (actual_block_supported F).2 p
  have hPair : (fun p q => trace (C p * B q) : Matrix (SymIndex 3) (SymIndex 3) ℝ) = positiveGram 3 := by
    ext p q
    rw [show trace (C p * B q) = trace (leadingRows F.val.1 p * leadingRows F.val.2 q) from
      supported_frame_trace_compression _ _ T hT (hA p) (hs p)]
    exact (actual_block_trace F (Sum.inl p) (Sum.inl q)).trans (block_gram_leading r p q)
  apply coordinate_det_ne_zero_of_full_trace_rank C B hC
  rw [hPair, positive_gram_rank, symmetricIndex_card]

theorem actual_orientation_polynomial_ne_zero {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) :
    orientationPolynomial (leadingRows F.val.1) ≠ 0 := by
  obtain ⟨T,hT,hRange⟩ := actual_leading_frame F
  have hA : ∀ p, (leadingRows F.val.1 p).transpose = leadingRows F.val.1 p := by
    intro p
    ext a b
    simpa only [leadingRows, blockRows, Matrix.transpose_apply, star_trivial] using
      (F.property.1 (Fintype.equivFin (BlockIndex r) (Sum.inl p))).isHermitian.apply a b
  have hs : ∀ p, image (leadingRows F.val.1 p) ≤ LinearMap.range (Matrix.toEuclideanLin T) := by
    intro p
    rw [hRange]
    exact (actual_block_supported F).2 p
  rw [orientation_polynomial_supported _ hA T hT hs]
  exact mul_ne_zero (actual_leading_coordinate_det_ne_zero F T hT hRange) (frame_weight_pos T hT).ne'

theorem actual_orthogonal_orientation_product_pos {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r))
    (O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ) (hO : O * O.transpose = 1) :
    0 < orientationPolynomial (leadingRows F.val.1) *
      orientationPolynomial (fun p => O.transpose * leadingRows F.val.1 p * O) := by
  obtain ⟨T,hT,hRange⟩ := actual_leading_frame F
  have hA : ∀ p, (leadingRows F.val.1 p).transpose = leadingRows F.val.1 p := by
    intro p
    ext a b
    simpa only [leadingRows, blockRows, Matrix.transpose_apply, star_trivial] using
      (F.property.1 (Fintype.equivFin (BlockIndex r) (Sum.inl p))).isHermitian.apply a b
  have hs : ∀ p, image (leadingRows F.val.1 p) ≤ LinearMap.range (Matrix.toEuclideanLin T) := by
    intro p
    rw [hRange]
    exact (actual_block_supported F).2 p
  have heq : leadingRows F.val.1 = (fun p => T * (T.transpose * leadingRows F.val.1 p * T) * T.transpose) := by
    funext p
    exact (supported_frame_reconstruct _ T hT (hA p) (hs p)).symm
  have hC : ∀ p, (T.transpose * leadingRows F.val.1 p * T).transpose = T.transpose * leadingRows F.val.1 p * T := by
    intro p
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA p, Matrix.mul_assoc]
  have hp := orthogonal_lift_orientation_product_pos T hT _ hC
    (actual_leading_coordinate_det_ne_zero F T hT hRange) O hO
  rw [heq]
  exact hp

#print axioms actual_leading_frame
#print axioms actual_leading_coordinate_det_ne_zero
#print axioms actual_orientation_polynomial_ne_zero
#print axioms actual_orthogonal_orientation_product_pos
end Reference.PF02GlobalOrientation
