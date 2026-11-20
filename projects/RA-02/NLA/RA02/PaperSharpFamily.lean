module

public import NLA.RA02.PaperSharpDefinitions
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
namespace NLA.RA02.Paper

theorem lower_diag (n : ℕ) (t : ℝ) (i : Fin n) : lower n t i i = 1 := by simp [lower]

theorem lower_triangular (n : ℕ) (t : ℝ) : (lower n t).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  simp [lower, ne_of_lt hij, not_lt_of_ge hij.le]

theorem lower_det (n : ℕ) (t : ℝ) : (lower n t).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (lower_triangular n t)]
  simp [lower_diag]

theorem lower_isUnit (n : ℕ) (t : ℝ) : IsUnit (lower n t) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  simp [lower_det]

theorem lower_zero (n : ℕ) : lower n 0 = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [lower, hij, Matrix.one_apply]

theorem continuous_lower (n : ℕ) : Continuous (lower n) := by
  apply continuous_matrix
  intro i j
  unfold lower
  split_ifs <;> fun_prop

theorem lower_tendsto_one (n : ℕ) : Filter.Tendsto (lower n) (𝓝[>] 0) (𝓝 1) := by
  simpa only [lower_zero] using (continuous_lower n).continuousAt.tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)

theorem sharpFamily_posDef (n : ℕ) (t : ℝ) (ht : 0 < t) : (sharpFamily n t).PosDef := by
  have hd : (diagonalScales n t).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact pow_pos (pow_pos ht _) _
  simpa only [sharpFamily, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr (lower_isUnit n t))

theorem lower_nonneg (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (i j : Fin n) : 0 ≤ lower n t i j := by
  unfold lower
  split_ifs <;> positivity

theorem lower_first_pos (n : ℕ) (t : ℝ) (ht : 0 < t) (i : Fin (n+1)) :
    0 < lower (n+1) t i 0 := by
  by_cases hi : i = 0
  · simp [lower, hi]
  · have hlt : (0 : Fin (n+1)) < i := Fin.pos_iff_ne_zero.mpr hi
    simp only [lower, if_neg hi, if_pos hlt]
    positivity

theorem sharpFamily_entry_pos (n : ℕ) (t : ℝ) (ht : 0 < t) (i j : Fin (n+1)) :
    0 < sharpFamily (n+1) t i j := by
  change 0 < ∑ a, (lower (n+1) t * diagonalScales (n+1) t) i a * lower (n+1) t j a
  simp only [diagonalScales, Matrix.mul_diagonal]
  apply Finset.sum_pos'
  · intro a _
    exact mul_nonneg (mul_nonneg (lower_nonneg _ _ ht.le _ _) (pow_nonneg (pow_nonneg ht.le _) _))
      (lower_nonneg _ _ ht.le _ _)
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    simpa using mul_pos (lower_first_pos n t ht i) (lower_first_pos n t ht j)

theorem sharpFamily_det (n : ℕ) (t : ℝ) :
    (sharpFamily n t).det = epsilon n t ^ (n*(n-1)/2) := by
  simp only [sharpFamily, Matrix.det_mul, Matrix.det_transpose, lower_det, one_mul, mul_one,
    diagonalScales, Matrix.det_diagonal]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

#print axioms sharpFamily_posDef
end NLA.RA02.Paper
