module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RootRA02CauchyProduct

def cauchyMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (x i + y j)⁻¹

def differences {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, (x j - x i)

def sums {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∏ i, ∏ j, (x i + y j)

end RootRA02CauchyProduct
