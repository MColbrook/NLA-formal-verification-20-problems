module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open Polynomial
namespace NLA.RA02.Paper

theorem cauchy_kernel_trivial {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0) (hcard : Fintype.card κ ≤ Fintype.card ι)
    (v : κ → ℝ) (hv : ∀ i, ∑ j, (x i + y j)⁻¹ * v j = 0) : v = 0 := by
  classical
  let P : ℝ[X] := ∑ j : κ, C (v j) * ∏ k ∈ Finset.univ.erase j, (X + C (y k))
  have hdegree : P.natDegree ≤ Fintype.card κ - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_prod_le _ _).trans
    simp
  have heval (i : ι) : P.eval (x i) = 0 := by
    have hterm (j : κ) : v j * (∏ k ∈ Finset.univ.erase j, (x i + y k)) =
        (∏ k, (x i + y k)) * ((x i + y j)⁻¹ * v j) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun k => x i + y k) (Finset.mem_univ j)]
      field_simp [hxy i j]
    calc
      P.eval (x i) = ∑ j, v j * (∏ k ∈ Finset.univ.erase j, (x i + y k)) := by
        simp only [P, eval_finsetSum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
      _ = (∏ k, (x i + y k)) * (∑ j, (x i + y j)⁻¹ * v j) := by
        simp_rw [hterm]
        exact (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hv i, mul_zero]
  funext j
  have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨j⟩
  have hP : P = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    P hx heval (by omega)
  have hself : P.eval (-y j) = v j * (∏ k ∈ Finset.univ.erase j, (-y j + y k)) := by
    simp only [P, eval_finset_sum, eval_mul, eval_C, eval_prod, eval_add, eval_X]
    apply Finset.sum_eq_single j
    · intro q _ hq
      have hp : (∏ k ∈ Finset.univ.erase q, (-y j + y k)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hq, Finset.mem_univ j⟩)
        ring
      rw [hp, mul_zero]
    · simp
  have hprod : (∏ k ∈ Finset.univ.erase j, (-y j + y k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk hz
    have he : y k = y j := by linarith
    exact (Finset.mem_erase.mp hk).1 (hy he)
  rw [hP, eval_zero] at hself
  exact (mul_eq_zero.mp hself.symm).resolve_right hprod

theorem cauchy_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : ι → ℝ) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0) :
    Matrix.det (fun i j => (x i + y j)⁻¹ : Matrix ι ι ℝ) ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  apply cauchy_kernel_trivial x y hx hy hxy le_rfl v
  intro i
  exact congrFun hzero i

#print axioms cauchy_det_ne_zero
end NLA.RA02.Paper
