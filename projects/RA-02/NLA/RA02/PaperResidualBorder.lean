module

public import NLA.RA02.PaperResidualDefinitions
public import NLA.RA02.PaperBordered
public import NLA.RA02.PaperPrefixFactorization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem residual_bordered_determinant {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
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

theorem interpolation_component_eventually_nonzero {n s : ℕ} (hs : s < n)
    (rows : Fin s ↪ Fin n) (i : Fin n) (hi : i ∉ Set.range rows) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, interpolationResidual hs rows t i ≠ 0 := by
  filter_upwards [prefix_eventually_nonsingular hs.le rows,
    prefix_eventually_nonsingular (Nat.succ_le_of_lt hs) (appendEmbedding rows i hi)] with t hu hb
  have he := prefix_bordered_determinant hs rows i hi t
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hu))
  rw [he] at hb
  exact (mul_ne_zero_iff.mp hb).2

#print axioms residual_bordered_determinant
end NLA.RA02.Paper
