module

public import NLA.PF02.PaperSymmetricDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper
variable {R : Type*} [CommRing R] {n : ℕ}

theorem symmetricMatrix_transpose (v : SymIndex n → R) :
    (symmetricMatrix v).transpose = symmetricMatrix v := by
  ext i j
  simp only [Matrix.transpose_apply, symmetricMatrix]
  split_ifs with hji hij hij
  · have : i = j := le_antisymm hij hji
    subst j
    rfl
  · rfl
  · rfl
  · omega

theorem coordinates_matrix (v : SymIndex n → R) :
    symmetricCoordinates (symmetricMatrix v) = v := by
  funext p
  simp [symmetricCoordinates, symmetricMatrix, p.property]

theorem matrix_coordinates (X : Matrix (Fin n) (Fin n) R) (hX : X.transpose = X) :
    symmetricMatrix (symmetricCoordinates X) = X := by
  ext i j
  dsimp [symmetricMatrix, symmetricCoordinates]
  split_ifs
  · rfl
  · exact congrFun (congrFun hX i) j

def coordinatesEquiv : symmetricSpace n R ≃ₗ[R] (SymIndex n → R) where
  toFun X := symmetricCoordinates X.val
  invFun v := ⟨symmetricMatrix v, symmetricMatrix_transpose v⟩
  left_inv X := Subtype.ext (matrix_coordinates X.val X.property)
  right_inv := coordinates_matrix
  map_add' X Y := rfl
  map_smul' c X := rfl

def coordinateAction (S : Matrix (Fin n) (Fin n) R) :
    (SymIndex n → R) →ₗ[R] (SymIndex n → R) :=
  coordinatesEquiv.toLinearMap ∘ₗ symmetricCongruence S ∘ₗ coordinatesEquiv.symm.toLinearMap

def congruenceMatrix (S : Matrix (Fin n) (Fin n) R) : Matrix (SymIndex n) (SymIndex n) R :=
  LinearMap.toMatrix (Pi.basisFun R (SymIndex n)) (Pi.basisFun R (SymIndex n))
    (coordinateAction S)

theorem coordinateAction_apply (S : Matrix (Fin n) (Fin n) R) (v : SymIndex n → R) :
    coordinateAction S v = symmetricCoordinates (S.transpose * symmetricMatrix v * S) := rfl

theorem coordinateAction_one : coordinateAction (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext v p
  simp [coordinateAction_apply, coordinates_matrix]

theorem coordinateAction_mul (A B : Matrix (Fin n) (Fin n) R) :
    coordinateAction (A * B) = coordinateAction B * coordinateAction A := by
  apply LinearMap.ext
  intro v
  funext p
  have hs : (A.transpose * symmetricMatrix v * A).transpose = A.transpose * symmetricMatrix v * A := by
    simp [Matrix.transpose_mul, symmetricMatrix_transpose, Matrix.mul_assoc]
  simp only [Module.End.mul_apply, coordinateAction_apply]
  rw [matrix_coordinates _ hs]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

theorem congruenceMatrix_one : congruenceMatrix (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [congruenceMatrix, coordinateAction_one]

theorem congruenceMatrix_mul (A B : Matrix (Fin n) (Fin n) R) :
    congruenceMatrix (A * B) = congruenceMatrix B * congruenceMatrix A := by
  simp only [congruenceMatrix, coordinateAction_mul, LinearMap.toMatrix_mul]

end NLA.PF02.Paper
