module

public import NLA.RA02.PaperInterpolationDefinitions
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper

def appendEmbedding {n s : ℕ} (rows : Fin s ↪ Fin n) (i : Fin n) (hi : i ∉ Set.range rows) :
    Fin (s+1) ↪ Fin n := ⟨Fin.snoc rows i, Fin.snoc_injective_of_injective rows.injective hi⟩

def borderedMatrix {s : ℕ} (M : Matrix (Fin s) (Fin s) ℝ) (u v : Fin s → ℝ) (a : ℝ) :
    Matrix (Fin (s+1)) (Fin (s+1)) ℝ :=
  (Matrix.fromBlocks M (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) j => v j)
    (fun (_ _ : Fin 1) => a)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem bordered_determinant {s : ℕ} (M : Matrix (Fin s) (Fin s) ℝ)
    (u v : Fin s → ℝ) (a : ℝ) (hu : IsUnit M) :
    (borderedMatrix M u v a).det = M.det * (a - v ⬝ᵥ (M⁻¹ *ᵥ u)) := by
  cases hu.nonempty_invertible
  rw [borderedMatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁,
    Matrix.invOf_eq_nonsing_inv]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, dotProduct, Matrix.mulVec]
  apply congrArg (a - ·)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem submatrix_append_eq_border {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (i j : Fin n) (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols) :
    A.submatrix (appendEmbedding rows i hi) (appendEmbedding cols j hj) =
      borderedMatrix (A.submatrix rows cols) (fun k => A (rows k) j) (fun k => A i (cols k)) (A i j) := by
  ext k l
  induction k using Fin.lastCases <;> induction l using Fin.lastCases <;>
    simp [appendEmbedding, borderedMatrix, Matrix.submatrix_apply]

theorem prefix_append_eq_border {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (i : Fin n) (hi : i ∉ Set.range rows) (t : ℝ) :
    prefixMatrix (Nat.succ_le_of_lt hs) (appendEmbedding rows i hi) t =
      borderedMatrix (prefixMatrix hs.le rows t) (fun k => nextColumn hs t (rows k))
        (fun k => lower n t i (Fin.castLE hs.le k)) (nextColumn hs t i) := by
  ext k l
  induction k using Fin.lastCases <;> induction l using Fin.lastCases <;>
    simp [prefixMatrix, appendEmbedding, borderedMatrix, Matrix.submatrix_apply, nextColumn] <;> rfl

theorem prefix_bordered_determinant {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (i : Fin n) (hi : i ∉ Set.range rows) (t : ℝ) (hu : IsUnit (prefixMatrix hs.le rows t)) :
    (prefixMatrix (Nat.succ_le_of_lt hs) (appendEmbedding rows i hi) t).det =
      (prefixMatrix hs.le rows t).det * interpolationResidual hs rows t i := by
  rw [prefix_append_eq_border, bordered_determinant _ _ _ _ hu]
  rfl

#print axioms prefix_bordered_determinant
end NLA.RA02.Paper
