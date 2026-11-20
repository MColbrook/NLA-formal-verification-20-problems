module

public import NLA.RA02.PaperResidualCharacterization
public import NLA.RA02.PaperPivotDefinitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper

theorem residual_append_update {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (p q : Fin n) (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols))
    (ha : IsUnit (A.submatrix (appendEmbedding rows p hp) (appendEmbedding cols q hq))) :
    crossUpdate (interpolatoryResidual A rows cols) p q =
      interpolatoryResidual A (appendEmbedding rows p hp) (appendEmbedding cols q hq) := by
  let R := interpolatoryResidual A rows cols
  let X := (A.submatrix rows cols)⁻¹ * A.submatrix rows id
  let z := fun j => R p j / R p q
  let Z : Matrix (Fin (s+1)) (Fin n) ℝ := Fin.snoc (fun k j => X k j - X k q * z j) z
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
end NLA.RA02.Paper
