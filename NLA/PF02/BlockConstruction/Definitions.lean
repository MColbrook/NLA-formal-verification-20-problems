module

public import NLA.PF02.PositiveBasis.Definitions
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

abbrev Axis (r : ℕ) := Fin 3 ⊕ Fin r
abbrev BlockIndex (r : ℕ) := SymIndex 3 ⊕ (SymIndex r ⊕ (Fin 3 × Fin r))

def leadingEmbed {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Axis r) (Axis r) ℝ :=
  Matrix.fromBlocks H 0 0 0

def trailingEmbed {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) : Matrix (Axis r) (Axis r) ℝ :=
  Matrix.fromBlocks 0 0 0 H

def offDiagonalPositive {α : Type*} [DecidableEq α] (i j : α) : Matrix α α ℝ :=
  fun a b => 2 * (if a = b then 1 else 0) + (if a = i ∧ b = j then 1 else 0) +
    (if a = j ∧ b = i then 1 else 0)

def blockFactor (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℝ
  | Sum.inl p => leadingEmbed (positiveMatrix p)
  | Sum.inr (Sum.inl p) => trailingEmbed (positiveMatrix p)
  | Sum.inr (Sum.inr ij) => offDiagonalPositive (Sum.inl ij.1) (Sum.inr ij.2)

def blockGram (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℝ :=
  fun p q => trace (blockFactor r p * blockFactor r q)

def finiteBlockFactor (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  (blockFactor r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def finiteBlockGram (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℝ :=
  traceGram (finiteBlockFactor r)

def blockFactorInt (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℤ
  | Sum.inl p => Matrix.fromBlocks (positiveMatrixInt p) 0 0 0
  | Sum.inr (Sum.inl p) => Matrix.fromBlocks 0 0 0 (positiveMatrixInt p)
  | Sum.inr (Sum.inr ij) => fun a b => 2 * (if a = b then 1 else 0) +
      (if a = Sum.inl ij.1 ∧ b = Sum.inr ij.2 then 1 else 0) +
      (if a = Sum.inr ij.2 ∧ b = Sum.inl ij.1 then 1 else 0)

def finiteBlockFactorInt (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℤ :=
  (blockFactorInt r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def finiteBlockGramInt (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℤ :=
  fun p q => trace (finiteBlockFactorInt r p * finiteBlockFactorInt r q)

end Reference.PF02BlockConstruction
