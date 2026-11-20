module

public import NLA.PF02.GlobalOrientation.Coordinates
public import NLA.PF02.SupportBridge.FrameCompression
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

theorem sliced_lift {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (C : Matrix (Fin 3) (Fin 3) ℝ) (e : Fin 3 → Fin k) :
    (T * C * T.transpose).submatrix e e =
      T.submatrix e id * C * (T.submatrix e id).transpose := by
  rw [Matrix.submatrix_mul _ _ e id e Function.bijective_id,
    Matrix.submatrix_mul _ _ e id id Function.bijective_id]
  rfl

theorem orientation_polynomial_lift {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (C : SymIndex 3 → Matrix (Fin 3) (Fin 3) ℝ) (hC : ∀ p, (C p).transpose = C p) :
    orientationPolynomial (fun p => T * C p * T.transpose) =
      (coordinateRows C).det * frameWeight T := by
  simp only [orientationPolynomial, frameWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sliced_lift]
  have h := coordinate_rows_congruence_det C hC (T.submatrix e id).transpose
  simpa only [Matrix.transpose_transpose, Matrix.det_transpose] using h

theorem orthonormal_frame_has_nonzero_minor {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (hT : T.transpose * T = 1) :
    ∃ e : Fin 3 → Fin k, (T.submatrix e id).det ≠ 0 := by
  classical
  have hl := Matrix.rank_mul_le_right T.transpose T
  have hu := Matrix.rank_le_card_width T
  have hR : T.rank = 3 := by
    rw [hT, Matrix.rank_one, Fintype.card_fin] at hl
    simp only [Fintype.card_fin] at hu
    omega
  have hdim : Module.finrank ℝ (Submodule.span ℝ (Set.range T.row)) = 3 := by
    rw [← Matrix.rank_eq_finrank_span_row, hR]
  obtain ⟨f, hf, _, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range T.row)
  choose e he using fun i : Fin 3 => hf (Fin.cast hdim.symm i)
  refine ⟨e, Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_row ?_)⟩
  have hi := hlin.comp (fun i : Fin 3 => Fin.cast hdim.symm i) (Fin.cast_injective _)
  have heq : (T.submatrix e id).row = f ∘ (fun i : Fin 3 => Fin.cast hdim.symm i) := by
    funext i j
    exact congrFun (he i) j
  rw [heq]
  exact hi

theorem frame_weight_pos {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ)
    (hT : T.transpose * T = 1) : 0 < frameWeight T := by
  classical
  obtain ⟨e, he⟩ := orthonormal_frame_has_nonzero_minor T hT
  apply Finset.sum_pos' (fun e _ => by positivity)
  exact ⟨e, Finset.mem_univ e, by positivity⟩

theorem supported_frame_reconstruct {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (T : Matrix (Fin k) (Fin 3) ℝ) (hT : T.transpose * T = 1)
    (hA : A.transpose = A)
    (hs : Reference.PF02Support.image A ≤ LinearMap.range (Matrix.toEuclideanLin T)) :
    T * (T.transpose * A * T) * T.transpose = A := by
  have hl := Reference.PF02Support.supported_frame_left_projection A T hT hs
  have hr := Reference.PF02Support.supported_frame_right_projection A T hT hA hs
  calc
    T * (T.transpose * A * T) * T.transpose = (T * T.transpose * A) * T * T.transpose := by
      simp only [Matrix.mul_assoc]
    _ = A * T * T.transpose := by rw [hl]
    _ = A := hr

theorem orientation_polynomial_supported {k : ℕ}
    (A : SymIndex 3 → Matrix (Fin k) (Fin k) ℝ) (hA : ∀ p, (A p).transpose = A p)
    (T : Matrix (Fin k) (Fin 3) ℝ) (hT : T.transpose * T = 1)
    (hs : ∀ p, Reference.PF02Support.image (A p) ≤ LinearMap.range (Matrix.toEuclideanLin T)) :
    orientationPolynomial A =
      (coordinateRows (fun p => T.transpose * A p * T)).det * frameWeight T := by
  have hC : ∀ p, (T.transpose * A p * T).transpose = T.transpose * A p * T := by
    intro p
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA p, Matrix.mul_assoc]
  have h := orientation_polynomial_lift T (fun p => T.transpose * A p * T) hC
  simpa only [supported_frame_reconstruct _ T hT (hA _) (hs _)] using h

#print axioms sliced_lift
#print axioms orientation_polynomial_lift
#print axioms orthonormal_frame_has_nonzero_minor
#print axioms frame_weight_pos
#print axioms supported_frame_reconstruct
#print axioms orientation_polynomial_supported
end Reference.PF02GlobalOrientation
