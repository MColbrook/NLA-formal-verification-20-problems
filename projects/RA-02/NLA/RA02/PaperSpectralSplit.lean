module

public import NLA.RA02.PaperSharpFamily

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
namespace NLA.RA02.Paper

def scaledSpectralTail {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ := fun i j =>
  ∑ k : Fin n, if s ≤ k.val then
    lower n t (rows i) k * epsilon n t^(k.val-s) * lower n t (cols j) k else 0

theorem continuous_scaledSpectralTail {n s : ℕ} (rows cols : Fin s ↪ Fin n) :
    Continuous (scaledSpectralTail rows cols) := by
  apply continuous_matrix
  intro i j
  unfold scaledSpectralTail
  apply continuous_finsetSum
  intro k _
  split_ifs
  · exact (((continuous_lower n).matrix_elem _ _).mul
      ((continuous_id.pow _).pow _)).mul ((continuous_lower n).matrix_elem _ _)
  · exact continuous_const

theorem sum_initial_segment {n s : ℕ} (hs : s ≤ n) (f : Fin n → ℝ) :
    (∑ k : Fin n, if k.val < s then f k else 0) = ∑ k : Fin s, f (Fin.castLE hs k) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => Fin.castLE hs i)
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun x : Fin n => x.val) hij)
  · intro j hj
    have hj' : j.val < s := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val,hj'⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

theorem sharpFamily_entry_sum (n : ℕ) (t : ℝ) (i j : Fin n) :
    sharpFamily n t i j = ∑ k : Fin n,
      lower n t i k * epsilon n t^k.val * lower n t j k := by
  rw [sharpFamily, diagonalScales, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

theorem spectral_split {n s : ℕ} (hs : s ≤ n) (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    (sharpFamily n t).submatrix rows cols =
      prefixMatrix hs rows t * Matrix.diagonal (fun j : Fin s => epsilon n t^j.val) *
        (prefixMatrix hs cols t).transpose +
      epsilon n t^s • scaledSpectralTail rows cols t := by
  ext i j
  simp only [Matrix.submatrix_apply, sharpFamily_entry_sum, Matrix.add_apply, Matrix.smul_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    smul_eq_mul, prefixMatrix, Matrix.submatrix_apply, Fin.val_castLE, scaledSpectralTail]
  erw [← sum_initial_segment hs (fun k =>
    lower n t (rows i) k * epsilon n t^k.val * lower n t (cols j) k)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.val < s
  · simp [hk, Nat.not_le.mpr hk]
  · have hks : s ≤ k.val := Nat.le_of_not_gt hk
    simp only [if_neg hk, if_pos hks, zero_add]
    have hp : epsilon n t^k.val = epsilon n t^s * epsilon n t^(k.val-s) := by
      rw [← pow_add, Nat.add_sub_of_le hks]
    rw [hp]
    ring

#print axioms spectral_split

end NLA.RA02.Paper
