module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.IS03.GeneralNewton

def rootPolynomial {ι : Type*} [Fintype ι] (μ : ι → ℂ) : ℂ[X] :=
  ∏ i, (X - C (μ i))

def coefficient {ι : Type*} [Fintype ι] (μ : ι → ℂ) (j : ℕ) : ℂ :=
  if j ≤ Fintype.card ι then (rootPolynomial μ).coeff (Fintype.card ι-j) else 0

def powerSum {ι : Type*} [Fintype ι] (μ : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ i, μ i^k

end NLA.IS03.GeneralNewton
