module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema

def realizations {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ) :
    Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∀ i j, (L i j : ℝ) ≤ A i j ∧ A i j ≤ (U i j : ℝ)}

def solutions {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) :
    Set (Fin n → ℝ) :=
  {x | ∃ A ∈ realizations L U, A *ᵥ x = fun i => (b i : ℝ)}

def lowerRow {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (s : Fin n → Bool) : Matrix (Fin m) (Fin n) ℚ :=
  fun i j => if s j then L i j else U i j

def upperRow {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (s : Fin n → Bool) : Matrix (Fin m) (Fin n) ℚ :=
  fun i j => if s j then U i j else L i j

def inOrthant {n : ℕ} (s : Fin n → Bool) (x : Fin n → ℝ) : Prop :=
  ∀ j, if s j then 0 ≤ x j else x j ≤ 0

def rowBounds {m n : ℕ} (L U : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) (s : Fin n → Bool) (x : Fin n → ℝ) : Prop :=
  ∀ i, (∑ j, (lowerRow L U s i j : ℝ) * x j) ≤ (b i : ℝ) ∧
    (b i : ℝ) ≤ ∑ j, (upperRow L U s i j : ℝ) * x j

end Reference.IV04RationalBoxExtrema
