module

public import NLA.RA08.PaperDerivativeDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA08.Paper

theorem diagonalSylvesterInverse_add {n : ℕ} (a : Fin n → ℝ) (F G : RealMatrix n) :
    diagonalSylvesterInverse a (F+G) = diagonalSylvesterInverse a F+diagonalSylvesterInverse a G := by
  ext i j
  exact add_div _ _ _

theorem diagonalSylvesterInverse_sub {n : ℕ} (a : Fin n → ℝ) (F G : RealMatrix n) :
    diagonalSylvesterInverse a (F-G) = diagonalSylvesterInverse a F-diagonalSylvesterInverse a G := by
  ext i j
  exact sub_div _ _ _

theorem diagonalSylvesterInverse_smul {n : ℕ} (a : Fin n → ℝ) (t : ℝ) (F : RealMatrix n) :
    diagonalSylvesterInverse a (t • F) = t • diagonalSylvesterInverse a F := by
  ext i j
  simp only [diagonalSylvesterInverse,Matrix.smul_apply,smul_eq_mul]
  ring

theorem diagonalSylvesterInverse_solve {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (F : RealMatrix n) :
    Matrix.diagonal a*diagonalSylvesterInverse a F+
      diagonalSylvesterInverse a F*Matrix.diagonal a=F := by
  ext i j
  simp only [Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,diagonalSylvesterInverse]
  have hd : a i+a j ≠ 0 := ne_of_gt (add_pos (ha i) (ha j))
  field_simp

theorem diagonalSylvesterInverse_cancel {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (F : RealMatrix n) :
    diagonalSylvesterInverse a (Matrix.diagonal a*F+F*Matrix.diagonal a)=F := by
  ext i j
  simp only [diagonalSylvesterInverse,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  have hd : a i+a j ≠ 0 := ne_of_gt (add_pos (ha i) (ha j))
  field_simp

theorem sylvester_remainder_identity {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (M E Y : RealMatrix n) (t : ℝ)
    (h0 : Matrix.diagonal a*Matrix.diagonal a=M*M)
    (ht : Y*Y=(M+t • E)*(M+t • E)) :
    Y-Matrix.diagonal a-t • diagonalSylvesterInverse a (M*E+E*M) =
      diagonalSylvesterInverse a (t^2 • (E*E)-(Y-Matrix.diagonal a)*(Y-Matrix.diagonal a)) := by
  let D := Y-Matrix.diagonal a
  have hL : Matrix.diagonal a*D+D*Matrix.diagonal a =
      t • (M*E+E*M)+t^2 • (E*E)-D*D := by
    calc
      _ = Y*Y-Matrix.diagonal a*Matrix.diagonal a-D*D := by dsimp [D];noncomm_ring
      _ = _ := by
        rw [ht,h0]
        simp only [mul_add,add_mul,smul_mul_assoc,mul_smul_comm,smul_smul,smul_add,pow_two]
        abel
  have hc := congrArg (diagonalSylvesterInverse a) hL
  rw [diagonalSylvesterInverse_cancel a ha D] at hc
  rw [diagonalSylvesterInverse_sub,diagonalSylvesterInverse_add,
    diagonalSylvesterInverse_smul,diagonalSylvesterInverse_smul] at hc
  rw [diagonalSylvesterInverse_sub,diagonalSylvesterInverse_smul]
  change D-t • diagonalSylvesterInverse a (M*E+E*M) = _
  rw [hc]
  abel

#print axioms sylvester_remainder_identity
end NLA.RA08.Paper
