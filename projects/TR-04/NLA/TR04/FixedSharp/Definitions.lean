module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.TR04.FixedSharp

abbrev Tensor := Matrix (Fin 3) (Fin 3 × Fin 2) ℝ

def family (α β γ : ℝ) : Tensor := fun i jk =>
  if i = 0 ∧ jk = (0, 0) then α else
  if i = 1 ∧ jk = (1, 0) then β else
  if i = 2 ∧ jk = (2, 1) then γ else 0

def secondCut (A : Tensor) : Matrix (Fin 3 × Fin 3) (Fin 2) ℝ :=
  fun ij k => A ij.1 (ij.2, k)

def normSq (A : Tensor) : ℝ := ∑ i, ∑ jk, A i jk ^ 2

def feasible (X : Tensor) : Prop := X.rank ≤ 2 ∧ (secondCut X).rank ≤ 1

def optimalError (A : Tensor) : ℝ := sInf {z | ∃ X : Tensor, feasible X ∧ z = normSq (A - X)}

def optimalCandidate (α β : ℝ) : Tensor := family α β 0

def firstCandidate (α γ : ℝ) : Tensor := family α 0 γ

def greedyCandidate (α : ℝ) : Tensor := family α 0 0

end NLA.TR04.FixedSharp
