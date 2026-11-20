module

public import NLA.PF02.PaperSymmetricDiagonal
public import NLA.PF02.PaperSymmetricTransvection

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.PF02.Paper

theorem congruenceMatrix_det {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    (congruenceMatrix S).det = S.det^(n+1) := by
  apply Matrix.diagonal_transvection_induction (fun A => (congruenceMatrix A).det = A.det^(n+1)) S
  · intro d _
    exact congruenceMatrix_diagonal_det d
  · intro t
    rw [t.det, one_pow]
    exact congruence_transvection_det t.i t.j t.hij t.c
  · intro A B hA hB
    rw [congruenceMatrix_mul, Matrix.det_mul, Matrix.det_mul, hA, hB, mul_pow, mul_comm]

theorem symmetricCongruence_det {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (symmetricCongruence S) = S.det^(n+1) := by
  have h := congruenceMatrix_det S
  rw [congruenceMatrix, LinearMap.det_toMatrix, coordinateAction,
    LinearMap.det_conj] at h
  exact h

#print axioms symmetricCongruence_det
end NLA.PF02.Paper
