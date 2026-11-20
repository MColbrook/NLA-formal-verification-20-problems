module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Real.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Tridiagonal {n : ℕ} (A : Mat n) : Prop :=
  ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → A i j = 0

def UnitSuperdiagonal {n : ℕ} (A : Mat (n+1)) : Prop :=
  ∀ i : Fin n, A i.castSucc i.succ=1

def cornerRhs (n : ℕ) : Fin (n+1) → ℝ := Pi.single (Fin.last n) (-1)

def unitedSolutions {n : ℕ} (S : Set (Mat (n+1))) : Set (Fin (n+1) → ℝ) :=
  {x | ∃ A ∈ S, A.mulVec x=cornerRhs n}

def firstCoordinateValues {n : ℕ} (S : Set (Mat (n+1))) : Set ℝ :=
  (fun x : Fin (n+1) → ℝ => x 0) '' unitedSolutions S

end IV04.Paper
