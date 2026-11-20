module

public import NLA.PF02.GlobalOrientation.Definitions
public import NLA.PF02.PaperSymmetricDeterminant

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

theorem coordinate_rows_congruence {n : ℕ} (C : SymIndex n → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ p, (C p).transpose = C p) (S : Matrix (Fin n) (Fin n) ℝ) :
    coordinateRows (fun p => S.transpose * C p * S) = coordinateRows C * (congruenceMatrix S).transpose := by
  ext p q
  have h := LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (SymIndex n))
    (Pi.basisFun ℝ (SymIndex n)) (coordinateAction S) (symmetricCoordinates (C p))
  have hp : (congruenceMatrix S *ᵥ symmetricCoordinates (C p)) q =
      symmetricCoordinates (S.transpose * C p * S) q := by
    simpa only [congruenceMatrix, Pi.basisFun_repr, Matrix.mulVec, dotProduct, coordinateAction_apply,
      matrix_coordinates _ (hC p)] using congrFun h q
  simpa [coordinateRows, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, symmetricCoordinates, mul_comm] using hp.symm

theorem coordinate_rows_congruence_det {n : ℕ}
    (C : SymIndex n → Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ p, (C p).transpose = C p) (S : Matrix (Fin n) (Fin n) ℝ) :
    (coordinateRows (fun p => S.transpose * C p * S)).det =
      (coordinateRows C).det * S.det ^ (n+1) := by
  rw [coordinate_rows_congruence C hC S, Matrix.det_mul, Matrix.det_transpose,
    congruenceMatrix_det]

#print axioms coordinate_rows_congruence
#print axioms coordinate_rows_congruence_det
end Reference.PF02GlobalOrientation
