module

public import NLA.PF02.GlobalOrientation.ActualNonzero

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02BlockSupportRecovery
open Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem rank_three_has_nonzero_minor {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (hR : T.rank = 3) : ∃ e : Fin 3 → Fin k, (T.submatrix e id).det ≠ 0 := by
  classical
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range T.row)) = 3 := by
    rw [← Matrix.rank_eq_finrank_span_row, hR]
  obtain ⟨f,hf,_,hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range T.row)
  choose e he using fun i : Fin 3 => hf (Fin.cast hdim.symm i)
  refine ⟨e, Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row ?_)⟩
  have hi := hlin.comp (fun i : Fin 3 => Fin.cast hdim.symm i) (Fin.cast_injective _)
  have heq : (T.submatrix e id).row = f ∘ (fun i : Fin 3 => Fin.cast hdim.symm i) := by
    funext i j
    exact congrFun (he i) j
  rw [heq]
  exact hi

theorem frame_weight_pos_of_rank {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (hR : T.rank = 3) : 0 < frameWeight T := by
  classical
  obtain ⟨e,he⟩ := rank_three_has_nonzero_minor T hR
  apply Finset.sum_pos' (fun e _ => by positivity)
  exact ⟨e,Finset.mem_univ e,by positivity⟩

theorem invertible_lift_orientation_product_pos {k : ℕ}
    (T : Matrix (Fin k) (Fin 3) ℝ) (hT : T.rank = 3)
    (C : SymIndex 3 → Matrix (Fin 3) (Fin 3) ℝ) (hC : ∀ p, (C p).transpose = C p)
    (hD : (coordinateRows C).det ≠ 0)
    (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.det ≠ 0) :
    0 < orientationPolynomial (fun p => T * C p * T.transpose) *
      orientationPolynomial (fun p => S.transpose * (T * C p * T.transpose) * S) := by
  let T' := S.transpose * T
  have hT' : T'.rank = 3 := by
    rw [Matrix.rank_mul_eq_right_of_det_ne_zero S.transpose T (by simpa using hS),hT]
  have heq : (fun p => S.transpose * (T * C p * T.transpose) * S) =
      (fun p => T' * C p * T'.transpose) := by
    funext p
    simp only [T',Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
  rw [heq,orientation_polynomial_lift T C hC,orientation_polynomial_lift T' C hC]
  have hp := mul_pos (sq_pos_of_ne_zero hD)
    (mul_pos (frame_weight_pos_of_rank T hT) (frame_weight_pos_of_rank T' hT'))
  nlinarith [hp]

theorem actual_invertible_orientation_product_pos {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r))
    (S : Matrix (Fin (3+r)) (Fin (3+r)) ℝ) (hS : S.det ≠ 0) :
    0 < orientationPolynomial (leadingRows F.val.1) *
      orientationPolynomial (fun p => S.transpose * leadingRows F.val.1 p * S) := by
  obtain ⟨T,hT,hRange⟩ := actual_leading_frame F
  have hR : T.rank = 3 := by
    have hl := Matrix.rank_mul_le_right T.transpose T
    have hu := Matrix.rank_le_card_width T
    rw [hT,Matrix.rank_one,Fintype.card_fin] at hl
    simp only [Fintype.card_fin] at hu
    omega
  have hA : ∀ p, (leadingRows F.val.1 p).transpose = leadingRows F.val.1 p := by
    intro p
    ext a b
    simpa only [leadingRows,blockRows,Matrix.transpose_apply,star_trivial] using
      (F.property.1 (Fintype.equivFin (BlockIndex r) (Sum.inl p))).isHermitian.apply a b
  have hs : ∀ p, image (leadingRows F.val.1 p) ≤ LinearMap.range (Matrix.toEuclideanLin T) := by
    intro p
    rw [hRange]
    exact (actual_block_supported F).2 p
  have heq : leadingRows F.val.1 =
      (fun p => T * (T.transpose * leadingRows F.val.1 p * T) * T.transpose) := by
    funext p
    exact (supported_frame_reconstruct _ T hT (hA p) (hs p)).symm
  have hC : ∀ p, (T.transpose * leadingRows F.val.1 p * T).transpose =
      T.transpose * leadingRows F.val.1 p * T := by
    intro p
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,hA p,Matrix.mul_assoc]
  have hp := invertible_lift_orientation_product_pos T hR _ hC
    (actual_leading_coordinate_det_ne_zero F T hT hRange) S hS
  rw [heq]
  exact hp

#print axioms rank_three_has_nonzero_minor
#print axioms frame_weight_pos_of_rank
#print axioms invertible_lift_orientation_product_pos
#print axioms actual_invertible_orientation_product_pos
end Reference.PF02GlobalOrientation
