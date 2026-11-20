module

public import NLA.RA02.ComplexHistoryDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper.ComplexHistory

theorem bordered_determinant {s : ℕ} (M : Matrix (Fin s) (Fin s) ℂ)
    (u v : Fin s → ℂ) (a : ℂ) (hu : IsUnit M) :
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

theorem submatrix_append_eq_border {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (i j : Fin n) (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols) :
    A.submatrix (appendEmbedding rows i hi) (appendEmbedding cols j hj) =
      borderedMatrix (A.submatrix rows cols) (fun k => A (rows k) j) (fun k => A i (cols k)) (A i j) := by
  ext k l
  induction k using Fin.lastCases <;> induction l using Fin.lastCases <;>
    simp [appendEmbedding, borderedMatrix, Matrix.submatrix_apply]

theorem residual_bordered_determinant {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (i j : Fin n) (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols)) :
    (A.submatrix (appendEmbedding rows i hi) (appendEmbedding cols j hj)).det =
      (A.submatrix rows cols).det * interpolatoryResidual A rows cols i j := by
  rw [submatrix_append_eq_border, bordered_determinant _ _ _ _ hu]
  congr 1
  simp only [interpolatoryResidual, Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    id_eq, dotProduct, Matrix.mulVec]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem residual_selected_row {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols)) (i : Fin s) (j : Fin n) :
    interpolatoryResidual A rows cols (rows i) j = 0 := by
  have hh : (A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id).submatrix rows id =
      A.submatrix rows cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
    rfl
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul] at hh
  have he := congrFun (congrFun hh i) j
  exact sub_eq_zero.mpr he.symm

theorem residual_selected_column {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols)) (i : Fin n) (j : Fin s) :
    interpolatoryResidual A rows cols i (cols j) = 0 := by
  have hh : (A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id).submatrix id cols =
      A.submatrix id cols * ((A.submatrix rows cols)⁻¹ * A.submatrix rows cols) := by
    rw [Matrix.mul_assoc]
    rfl
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one] at hh
  have he := congrFun (congrFun hh i) j
  exact sub_eq_zero.mpr he.symm

theorem residual_of_interpolating_coefficients {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols))
    (Z : Matrix (Fin s) (Fin n) ℂ)
    (hZ : ∀ i : Fin s, ∀ j : Fin n, (A - A.submatrix id cols * Z) (rows i) j = 0) :
    A - A.submatrix id cols * Z = interpolatoryResidual A rows cols := by
  have he : A.submatrix rows cols * Z = A.submatrix rows id := by
    ext i j
    have hh := hZ i j
    exact (sub_eq_zero.mp hh).symm
  have hz : Z = (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
    rw [← he, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul]
  rw [hz, ← Matrix.mul_assoc]
  rfl

theorem residual_append_update {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (rows cols : Fin s ↪ Fin n) (p q : Fin n) (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols))
    (ha : IsUnit (A.submatrix (appendEmbedding rows p hp) (appendEmbedding cols q hq))) :
    crossUpdate (interpolatoryResidual A rows cols) p q =
      interpolatoryResidual A (appendEmbedding rows p hp) (appendEmbedding cols q hq) := by
  let R := interpolatoryResidual A rows cols
  let X := (A.submatrix rows cols)⁻¹ * A.submatrix rows id
  let z := fun j => R p j / R p q
  let Z : Matrix (Fin (s+1)) (Fin n) ℂ := Fin.snoc (fun k j => X k j - X k q * z j) z
  have hr : R = A - A.submatrix id cols * X := by
    dsimp [R, X, interpolatoryResidual]
    rw [Matrix.mul_assoc]
  have hn : R p q ≠ 0 := by
    have hh := (Matrix.isUnit_iff_isUnit_det _).mp ha
    rw [isUnit_iff_ne_zero, residual_bordered_determinant A rows cols p q hp hq hu] at hh
    exact (mul_ne_zero_iff.mp hh).2
  have hrepr : A - A.submatrix id (appendEmbedding cols q hq) * Z = crossUpdate R p q := by
    ext i j
    change A i j - (A.submatrix id (appendEmbedding cols q hq) * Z) i j = R i j - R i q * R p j / R p q
    rw [mul_div_assoc]
    change A i j - (A.submatrix id (appendEmbedding cols q hq) * Z) i j = R i j - R i q * z j
    rw [hr]
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
    rw [Fin.sum_univ_castSucc]
    simp only [Z, appendEmbedding, Function.Embedding.coeFn_mk, Fin.snoc_castSucc, Fin.snoc_last]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    ring
  have hZ : ∀ k : Fin (s+1), ∀ j : Fin n,
      (A - A.submatrix id (appendEmbedding cols q hq) * Z) (appendEmbedding rows p hp k) j = 0 := by
    intro k j
    rw [hrepr]
    induction k using Fin.lastCases with
    | last =>
      simp only [appendEmbedding, Function.Embedding.coeFn_mk, Fin.snoc_last]
      change R p j - R p q * R p j / R p q = 0
      field_simp
      <;> ring
    | cast k =>
      simp only [appendEmbedding, Function.Embedding.coeFn_mk, Fin.snoc_castSucc]
      change R (rows k) j - R (rows k) q * R p j / R p q = 0
      simp only [R, residual_selected_row A rows cols hu, zero_mul, zero_div, sub_zero]
  exact hrepr.symm.trans (residual_of_interpolating_coefficients A
    (appendEmbedding rows p hp) (appendEmbedding cols q hq) ha Z hZ)

#print axioms residual_append_update
end NLA.RA02.Paper.ComplexHistory
