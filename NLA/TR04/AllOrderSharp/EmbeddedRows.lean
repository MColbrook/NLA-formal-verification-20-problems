module

public import NLA.TR04.AllOrderSharp.UniqueRows
public import NLA.TR04.ThreeModeCompletion.FiniteMatrix

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.TensorGrouping

variable {m n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem entry_norm_zero (A : Matrix (Fin m) κ ℝ)
    (hA : entryFrobeniusSq A = 0) : A = 0 := by
  ext i j
  have hrow : (∑ k, A i k ^ 2) ≤ entryFrobeniusSq A :=
    Finset.single_le_sum
      (fun l _ => Finset.sum_nonneg (fun k _ => sq_nonneg (A l k)))
      (Finset.mem_univ i)
  have hentry : A i j ^ 2 ≤ ∑ k, A i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (A i k)) (Finset.mem_univ j)
  have hz : A i j ^ 2 = 0 := le_antisymm
    (by simpa [hA] using hentry.trans hrow) (sq_nonneg _)
  change A i j = 0
  nlinarith

theorem entry_norm_sub_comm (A B : Matrix (Fin m) κ ℝ) :
    entryFrobeniusSq (A - B) = entryFrobeniusSq (B - A) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply]
  ring

/-- Unique best truncation persists under any orthonormal left embedding.
This permits the arbitrary signs and rotations of the actual SVD frames.
-/
theorem embedded_smallest_row_unique (V : Matrix (Fin m) (Fin n) ℝ)
    (hV : V.transpose * V = 1) (D : Matrix (Fin n) κ ℝ)
    (w : Fin n → ℝ)
    (hgram : ∀ i k, (∑ j, D i j * D k j) = if i = k then w i else 0)
    (i₀ : Fin n) (hsmall : ∀ i, i ≠ i₀ → w i₀ < w i)
    (X : Matrix (Fin m) κ ℝ) (hrank : X.rank < n)
    (herror : entryFrobeniusSq (V * D - X) ≤ w i₀) :
    X = V * Matrix.of (fun i j => if i = i₀ then 0 else D i j) := by
  let C := V.transpose * X
  have hC : C.rank < n := (Matrix.rank_mul_le_right _ _).trans_lt hrank
  have hcomp := finite_column_compression_frobenius_le V hV (V * D - X)
  have hcerror : entryFrobeniusSq (D - C) ≤ w i₀ := by
    have he : V.transpose * (V * D - X) = D - C := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hV, Matrix.one_mul]
    rw [he] at hcomp
    exact hcomp.trans herror
  let D' : Matrix (Fin n) κ ℝ := fun i j => if i = i₀ then 0 else D i j
  have hc : C = D' := smallest_row_unique D C w hgram i₀ hsmall hC hcerror
  have herr : entryFrobeniusSq (D - D') = w i₀ := by
    change (∑ i, ∑ j, (D i j - (if i = i₀ then 0 else D i j)) ^ 2) = w i₀
    rw [Finset.sum_eq_single i₀]
    · simpa [pow_two] using hgram i₀ i₀
    · intro i _ hi
      simp [hi]
    · simp
  have hdecomp := Reference.ThreeModeCompletion.finite_orthonormal_column_error_decomposition
    V hV X D
  rw [entry_norm_sub_comm X (V * D)] at hdecomp
  change entryFrobeniusSq (V * D - X) = entryFrobeniusSq (X - V * V.transpose * X) +
    entryFrobeniusSq (C - D) at hdecomp
  rw [hc, entry_norm_sub_comm D' D, herr] at hdecomp
  have hzero : entryFrobeniusSq (X - V * V.transpose * X) = 0 := by
    have hn : 0 ≤ entryFrobeniusSq (X - V * V.transpose * X) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    linarith
  have hback : X = V * C := by
    have hz := entry_norm_zero (X - V * V.transpose * X) hzero
    have hh := sub_eq_zero.mp hz
    simpa only [C, Matrix.mul_assoc] using hh
  rw [hback, hc]
  rfl

#print axioms embedded_smallest_row_unique

end NLA.TR04.AllOrderSharp
