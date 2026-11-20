module

public import NLA.PF02.GlobalOrientation.ActualDefinitions
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02PositiveBasis

def reflectedPair : SymIndex 3 := ⟨(0,1), by decide⟩

def reflectionDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

def reflectedPositive (p : SymIndex 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if p = reflectedPair then reflectionDiagonal.transpose * positiveMatrix p * reflectionDiagonal
  else positiveMatrix p

def reflectedBlockFactor (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℝ
  | Sum.inl p => leadingEmbed (reflectedPositive p)
  | Sum.inr p => blockFactor r (Sum.inr p)

def finiteReflectedBlockFactor (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  (reflectedBlockFactor r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def enumeratedReflectedFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  finiteReflectedBlockFactor r ((Fintype.equivFin (BlockIndex r)).symm i)

def canonicalLeadingFrame (r : ℕ) : Matrix (Fin (3+r)) (Fin 3) ℝ :=
  (Matrix.fromRows (1 : Matrix (Fin 3) (Fin 3) ℝ) (0 : Matrix (Fin r) (Fin 3) ℝ)).submatrix
    finSumFinEquiv.symm id

end Reference.PF02GlobalOrientation
