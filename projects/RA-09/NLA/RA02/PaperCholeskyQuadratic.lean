module

public import NLA.RA02.PaperPivotRotation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem quadratic_outer {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ (Matrix.vecMulVec u (star u) *ᵥ x) =
      ((Complex.normSq (star u ⬝ᵥ x) : ℝ) : ℂ) := by
  rw [Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp only [op_smul_eq_mul, Complex.normSq_eq_conj_mul_self]
  congr 1
  simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul, Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem choleskyStep_quadratic {n : ℕ} (A : NLA.RA02.Square n) (hA : A.IsHermitian)
    (x : Fin n → ℂ) (p : Fin n) (hp : A p p ≠ 0) :
    star x ⬝ᵥ (NLA.RA02.choleskyStep A p *ᵥ x) =
      star x ⬝ᵥ (A *ᵥ x) - ((Complex.normSq ((A *ᵥ x) p) : ℝ) : ℂ) / A p p := by
  have hr : star (fun i => A i p) ⬝ᵥ x = (A *ᵥ x) p := by
    apply Finset.sum_congr rfl
    intro i _
    have he : star (A i p) = A p i := congrFun (congrFun hA p) i
    simp only [Pi.star_apply, he]
  rw [choleskyStep_outer A hA p hp, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, quadratic_outer, hr]
  simp only [smul_eq_mul]
  ring

#print axioms choleskyStep_quadratic
end NLA.RA02.Paper
