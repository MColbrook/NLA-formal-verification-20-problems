module

public import NLA.PF02.PaperSymmetricDefinitions
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

def weight {n : ℕ} (p : SymIndex n) : ℝ := if p.val.1 = p.val.2 then 2 else 1

def positiveMatrix {n : ℕ} (p : SymIndex n) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + weight p • symmetricMatrix (Pi.single p 1)

def traceGram {ι : Type*} [Fintype ι] {n : ℕ}
    (F : ι → Matrix (Fin n) (Fin n) ℝ) : Matrix ι ι ℝ :=
  fun p q => trace (F p * F q)

def positiveGram (n : ℕ) : Matrix (SymIndex n) (SymIndex n) ℝ :=
  fun p q => trace (positiveMatrix p * positiveMatrix q)

def positiveMatrixInt {n : ℕ} (p : SymIndex n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => 2 * (if i = j then 1 else 0) +
    (if p.val.1 = p.val.2 then 2 else 1) * symmetricMatrix (Pi.single p 1) i j

def positiveGramInt (n : ℕ) : Matrix (SymIndex n) (SymIndex n) ℤ :=
  fun p q => trace (positiveMatrixInt p * positiveMatrixInt q)

end Reference.PF02PositiveBasis
