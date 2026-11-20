module

public import NLA.NM04.PositiveMargins.MinorRelation
public import NLA.NM04.DiagonalCovariance
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

theorem actual_balanced_kernel {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (hx : S (firstIndex hm) (firstIndex hn) ≠ 0)
    (ha0 : a (firstIndex hm) ≠ 0) (hb0 : b (firstIndex hn) ≠ 0)
    (hS : Margins S a b) (ha : ∑ i, a i = τ) :
    (pencil S hm hn a b τ (S (firstIndex hm) (firstIndex hn))).mulVec (fun _ => 1) = 0 := by
  have hdiag : (Matrix.diagonal (delta S hm hn)).mulVec (fun _ => 1) = delta S hm hn := by
    funext I
    rw [Matrix.mulVec_diagonal, mul_one]
  funext I
  simp only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVec_diagonal, mul_one]
  rw [← Matrix.mulVec_mulVec, hdiag, G_mulVec]
  change gamma S hm hn I + (S (firstIndex hm) (firstIndex hn) /
    (a (firstIndex hm) * b (firstIndex hn))) *
      action (fun i : Tail m => a i.val) (fun j : Tail n => b j.val) τ
        (delta S hm hn) I = 0
  calc
    _ = (S (firstIndex hm) (firstIndex hn) /
        (a (firstIndex hm) * b (firstIndex hn))) *
        (a (firstIndex hm) * b (firstIndex hn) * minor (tailMatrix S) I +
          action (fun i : Tail m => a i.val) (fun j : Tail n => b j.val) τ
            (delta S hm hn) I) := by
      unfold gamma
      field_simp [ha0, hb0] <;> ring
    _ = 0 := by rw [actual_minor_relation hm hn S a b τ hx ha0 hb0 hS ha I, mul_zero]

theorem actual_diagonal_covariance {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (τ z : ℝ) :
    pencil (diagonalScale A r c) hm hn a b τ z =
      pencil A hm hn a b τ z * Matrix.diagonal (covarianceFactor r c hm hn) := by
  have hd : delta (diagonalScale A r c) hm hn =
      fun I => covarianceFactor r c hm hn I * delta A hm hn I :=
    funext (fun I => (diagonal_minor_covariance hm hn A r c I).1)
  have hg : gamma (diagonalScale A r c) hm hn =
      fun I => covarianceFactor r c hm hn I * gamma A hm hn I :=
    funext (fun I => (diagonal_minor_covariance hm hn A r c I).2)
  ext I J
  simp only [pencil, hd, hg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal]
  by_cases h : I = J
  · subst J
    simp only [Matrix.diagonal_apply_eq]
    ring
  · simp only [Matrix.diagonal_apply_ne _ h]
    ring

/-- Exact manuscript equation for any actual positive diagonal scaling to the
prescribed margins. Only the positive pivot and first margins are divided by;
all other selected minors may vanish, including the empty tails. -/
theorem actual_general_determinant {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A : Rect m n) (hA : Positive A) (r : Fin m → ℝ) (c : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hS : Margins (diagonalScale A r c) a b) (hta : ∑ i, a i = τ)
    (_htb : ∑ j, b j = τ) :
    (pencil A hm hn a b τ
      (diagonalScale A r c (firstIndex hm) (firstIndex hn))).det = 0 := by
  let S := diagonalScale A r c
  let z := S (firstIndex hm) (firstIndex hn)
  have hx : z ≠ 0 := ne_of_gt (mul_pos (mul_pos (hr _) (hA _ _)) (hc _))
  have hnS := actual_balanced_kernel hm hn S a b τ hx
    (ne_of_gt (ha _)) (ne_of_gt (hb _)) hS hta
  let D := Matrix.diagonal (covarianceFactor r c hm hn)
  let v := D.mulVec (fun _ => 1)
  have hv : 0 < v (emptyIndex (Tail m) (Tail n)) := by
    simp only [v, D, Matrix.mulVec_diagonal, mul_one, covarianceFactor,
      emptyIndex, Finset.prod_empty, mul_one]
    exact mul_pos (hr _) (hc _)
  have hnull : (pencil A hm hn a b τ z).mulVec v = 0 := by
    calc
      _ = (pencil A hm hn a b τ z * D).mulVec (fun _ => 1) :=
        Matrix.mulVec_mulVec (fun _ => 1) (pencil A hm hn a b τ z) D
      _ = (pencil S hm hn a b τ z).mulVec (fun _ => 1) :=
        congrArg (fun M : Matrix (Index m n) (Index m n) ℝ => M.mulVec (fun _ => 1))
          (actual_diagonal_covariance hm hn A r c a b τ z).symm
      _ = 0 := hnS
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hnull
    (mem_nonZeroDivisors_iff_ne_zero.mpr (ne_of_gt hv))

#print axioms actual_balanced_kernel
#print axioms actual_diagonal_covariance
#print axioms actual_general_determinant
end
end NLA.NM04.PositiveMargins
