module

public import NLA.RA02.Definitions
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The printed lower-triangular factor, with paper indices shifted by one. -/
def lower (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then 1 else if j < i then t^(j.val+1) / (i.val+j.val+2 : ℕ) else 0

def epsilon (n : ℕ) (t : ℝ) : ℝ := t^(n^2)

def diagonalScales (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => epsilon n t ^ i.val)

/-- The exact L(t) D(t) L(t)^T family in the manuscript, in size n=r+1. -/
def sharpFamily (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lower n t * diagonalScales n t * (lower n t).transpose

def prefixMatrix {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ := (lower n t).submatrix rows (Fin.castLE hs)

def prefixDegree {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) : ℕ :=
  ∑ j : Fin s, if Fin.castLE hs j ∈ Set.range rows then 0 else j.val+1

end NLA.RA02.Paper
