module

public import NLA.PF02.BlockConstruction.EnumeratedDefinitions
public import NLA.PF02.SupportBridge.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

def coordinateRows {n : ℕ} (C : SymIndex n → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (SymIndex n) (SymIndex n) ℝ := fun p q => C p q.1.1 q.1.2

def orientationPolynomial {k : ℕ} (A : SymIndex 3 → Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ e : Fin 3 → Fin k, (coordinateRows (fun p => (A p).submatrix e e)).det

def frameWeight {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ) : ℝ :=
  ∑ e : Fin 3 → Fin k, (T.submatrix e id).det ^ 4

def reflectionMask {α : Type*} [DecidableEq α] (i j a b : α) : ℝ :=
  if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then -1 else 1

def entryReflection {α : Type*} [DecidableEq α] (i j : α) (A : Matrix α α ℝ) :
    Matrix α α ℝ := fun a b => reflectionMask i j a b * A a b

end Reference.PF02GlobalOrientation
