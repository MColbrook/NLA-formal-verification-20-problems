module

public import NLA.RA02.CauchyProduct.Recurrence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators

namespace RootRA02CauchyProduct

theorem sums_ne_zero {n : ℕ} (x y : Fin n → ℝ)
    (hne : ∀ i j, x i+y j ≠ 0) : sums x y ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => hne i j)

theorem determinant_product {n : ℕ} (x y : Fin n → ℝ)
    (hne : ∀ i j, x i+y j ≠ 0) :
    (cauchyMatrix x y).det = differences x * differences y / sums x y := by
  induction n with
  | zero => simp [differences, sums]
  | succ n ih =>
    have hr : (∏ i : Fin n, (x i.succ+y 0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hne i.succ 0)
    have hc : (∏ j : Fin n, (x 0+y j.succ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hne 0 j.succ)
    have ht : sums (x ∘ Fin.succ) (y ∘ Fin.succ) ≠ 0 :=
      sums_ne_zero _ _ (fun i j => hne i.succ j.succ)
    rw [determinant_succ x y hne,
      ih (x ∘ Fin.succ) (y ∘ Fin.succ) (fun i j => hne i.succ j.succ),
      differences_succ x, differences_succ y, sums_succ x y,
      Finset.prod_div_distrib, Finset.prod_div_distrib]
    field_simp [hne 0 0, hr, hc, ht]

theorem differences_pos {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) :
    0 < differences x := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (hx (Finset.mem_Ioi.mp hj))

theorem sums_pos {n : ℕ} (x y : Fin n → ℝ)
    (hpos : ∀ i j, 0 < x i+y j) : 0 < sums x y := by
  apply Finset.prod_pos
  intro i _
  exact Finset.prod_pos (fun j _ => hpos i j)

theorem actual_cauchy_determinant {n : ℕ} (x y : Fin n → ℝ)
    (hne : ∀ i j, x i+y j ≠ 0) :
    Matrix.det (fun i j => (x i+y j)⁻¹ : Matrix (Fin n) (Fin n) ℝ) =
      ((∏ i, ∏ j ∈ Finset.Ioi i, (x j-x i)) *
        (∏ i, ∏ j ∈ Finset.Ioi i, (y j-y i))) /
      (∏ i, ∏ j, (x i+y j)) := by
  exact determinant_product x y hne

theorem actual_cauchy_determinant_positive {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hpos : ∀ i j, 0 < x i+y j) :
    0 < Matrix.det (fun i j => (x i+y j)⁻¹ : Matrix (Fin n) (Fin n) ℝ) := by
  change 0 < (cauchyMatrix x y).det
  rw [determinant_product x y (fun i j => (hpos i j).ne')]
  exact div_pos (mul_pos (differences_pos x hx) (differences_pos y hy)) (sums_pos x y hpos)

theorem actual_cauchy_determinant_nonzero {n : ℕ} (x y : Fin n → ℝ)
    (hx : StrictMono x) (hy : StrictMono y) (hpos : ∀ i j, 0 < x i+y j) :
    Matrix.det (fun i j => (x i+y j)⁻¹ : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
  exact (actual_cauchy_determinant_positive x y hx hy hpos).ne'

theorem actual_empty_cauchy_determinant (x y : Fin 0 → ℝ) :
    Matrix.det (fun i j => (x i+y j)⁻¹ : Matrix (Fin 0) (Fin 0) ℝ) = 1 := by
  exact Matrix.det_fin_zero

#print axioms actual_cauchy_determinant
#print axioms actual_cauchy_determinant_positive
#print axioms actual_cauchy_determinant_nonzero
#print axioms actual_empty_cauchy_determinant
end RootRA02CauchyProduct
