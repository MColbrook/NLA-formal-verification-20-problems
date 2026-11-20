module

public import NLA.RA02.PaperHistoryDefinitions
public import NLA.RA03.Definitions
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper.ComplexHistory

def appendEmbedding {n s : ℕ} (rows : Fin s ↪ Fin n) (i : Fin n) (hi : i ∉ Set.range rows) :
    Fin (s+1) ↪ Fin n := ⟨Fin.snoc rows i, Fin.snoc_injective_of_injective rows.injective hi⟩

def borderedMatrix {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ) (u v : Fin s → ℂ) (a : ℂ) :
    Matrix (Fin (s+1)) (Fin (s+1)) ℂ :=
  (Matrix.fromBlocks M (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) j => v j)
    (fun (_ _ : Fin 1) => a)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def interpolatoryResidual {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  A - A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id

def crossUpdate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => A i j - A i q * A p j / A p q

def AllSquareMinorsNonzero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ s : ℕ, s ≤ n → ∀ rows cols : Fin s ↪ Fin n, (A.submatrix rows cols).det ≠ 0

end NLA.RA02.Paper.ComplexHistory
