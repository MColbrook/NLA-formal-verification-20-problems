module

public import NLA.RA02.CauchyProduct.Definitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
open Matrix

namespace RootRA02CauchyProduct

theorem differences_succ {n : ℕ} (x : Fin (n+1) → ℝ) :
    differences x = (∏ i : Fin n, (x i.succ-x 0)) * differences (x ∘ Fin.succ) := by
  simp only [differences, Fin.prod_univ_succ, Fin.Ioi_zero_eq_map,
    Finset.prod_map, Fin.coe_succEmb, Fin.prod_Ioi_succ, Function.comp_apply]

theorem sums_succ {n : ℕ} (x y : Fin (n+1) → ℝ) :
    sums x y = (x 0+y 0) * (∏ i : Fin n, (x i.succ+y 0)) *
      (∏ j : Fin n, (x 0+y j.succ)) * sums (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  simp only [sums, Fin.prod_univ_succ, Finset.prod_mul_distrib, Function.comp_apply]
  ring

theorem cauchy_entry_schur (a b c d : ℝ) (_hab : a+b ≠ 0)
    (hcb : c+b ≠ 0) (had : a+d ≠ 0) (hcd : c+d ≠ 0) :
    (c+d)⁻¹ - ((a+b)/(c+b)) * (a+d)⁻¹ =
      ((c-a)/(c+b)) * ((d-b)/(a+d)) * (c+d)⁻¹ := by
  field_simp
  ring

theorem determinant_succ {n : ℕ} (x y : Fin (n+1) → ℝ)
    (hne : ∀ i j, x i+y j ≠ 0) :
    (cauchyMatrix x y).det = (x 0+y 0)⁻¹ *
      (∏ i : Fin n, (x i.succ-x 0)/(x i.succ+y 0)) *
      (∏ j : Fin n, (y j.succ-y 0)/(x 0+y j.succ)) *
      (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det := by
  let c : Fin (n+1) → ℝ := Fin.cases 0 (fun i => -((x 0+y 0)/(x i.succ+y 0)))
  let W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    fun i j => cauchyMatrix x y i j + c i * cauchyMatrix x y 0 j
  have hd : W.det = (cauchyMatrix x y).det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (by intros; rfl)
  have h00 : W 0 0 = (x 0+y 0)⁻¹ := by simp [W, c, cauchyMatrix]
  have hs0 (i : Fin n) : W i.succ 0 = 0 := by
    simp only [W, c, cauchyMatrix, Fin.cases_succ]
    field_simp [hne 0 0, hne i.succ 0]
    ring
  have hsub : W.submatrix Fin.succ Fin.succ = Matrix.of (fun i j =>
      ((x i.succ-x 0)/(x i.succ+y 0)) *
        (((y j.succ-y 0)/(x 0+y j.succ)) *
          cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)) := by
    ext i j
    change (x i.succ+y j.succ)⁻¹ +
        (-((x 0+y 0)/(x i.succ+y 0))) * (x 0+y j.succ)⁻¹ =
      ((x i.succ-x 0)/(x i.succ+y 0)) *
        (((y j.succ-y 0)/(x 0+y j.succ)) * (x i.succ+y j.succ)⁻¹)
    rw [neg_mul, ← sub_eq_add_neg]
    exact (cauchy_entry_schur (x 0) (y 0) (x i.succ) (y j.succ)
      (hne 0 0) (hne i.succ 0) (hne 0 j.succ) (hne i.succ j.succ)).trans (by ring)
  have hscale : (W.submatrix Fin.succ Fin.succ).det =
      (∏ i : Fin n, (x i.succ-x 0)/(x i.succ+y 0)) *
      (∏ j : Fin n, (y j.succ-y 0)/(x 0+y j.succ)) *
      (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det := by
    rw [hsub]
    calc
      _ = (∏ i : Fin n, (x i.succ-x 0)/(x i.succ+y 0)) *
          (Matrix.of (fun i j => ((y j.succ-y 0)/(x 0+y j.succ)) *
            cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j)).det :=
        Matrix.det_mul_column _ _
      _ = _ := by rw [Matrix.det_mul_row]; ring
  rw [← hd, Matrix.det_succ_column_zero, Finset.sum_eq_single 0]
  · rw [Fin.succAbove_zero, hscale]
    simp only [Fin.val_zero, pow_zero, one_mul, h00]
    ring
  · intro i _ hi
    obtain ⟨j,rfl⟩ := i.eq_succ_of_ne_zero hi
    rw [hs0, mul_zero, zero_mul]
  · simp

#print axioms differences_succ
#print axioms sums_succ
#print axioms cauchy_entry_schur
#print axioms determinant_succ
end RootRA02CauchyProduct
