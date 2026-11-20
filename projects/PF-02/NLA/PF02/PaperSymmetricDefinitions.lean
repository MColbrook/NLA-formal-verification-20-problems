module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper

abbrev SymIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Upper-triangular coordinates, with the lower triangle filled symmetrically. -/
def symmetricMatrix (v : SymIndex n → R) : Matrix (Fin n) (Fin n) R := fun i j =>
  if h : i ≤ j then v ⟨(i,j), h⟩ else v ⟨(j,i), le_of_not_ge h⟩

def symmetricCoordinates (X : Matrix (Fin n) (Fin n) R) : SymIndex n → R :=
  fun p => X p.val.1 p.val.2

/-- The full space of symmetric matrices, including all singular matrices. -/
def symmetricSpace (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {X | X.transpose = X}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY; simp_all
  smul_mem' := by intro c X hX; simp_all

/-- The actual congruence map on the entire symmetric-matrix space. -/
def symmetricCongruence (S : Matrix (Fin n) (Fin n) R) :
    symmetricSpace n R →ₗ[R] symmetricSpace n R where
  toFun X := ⟨S.transpose * X.val * S, by
    have hx : X.val.transpose = X.val := X.property
    change (S.transpose * X.val * S).transpose = S.transpose * X.val * S
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hx, Matrix.mul_assoc]⟩
  map_add' X Y := by ext i j; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by ext i j; simp

end NLA.PF02.Paper
