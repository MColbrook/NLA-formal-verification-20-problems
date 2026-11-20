module

public import PaperDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace IV04.Paper

theorem corner_minor_det {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    (A.submatrix Fin.castSucc Fin.succ).det=1 := by
  have hlo : (A.submatrix Fin.castSucc Fin.succ).IsLowerTriangular := by
    intro i j hij
    apply ht
    left
    change i.val+1<j.val+1
    exact Nat.succ_lt_succ hij
  rw [Matrix.det_of_isLowerTriangular _ hlo]
  simp only [Matrix.submatrix_apply]
  exact Finset.prod_eq_one (fun i _ => hu i)

theorem corner_inverse_entry {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    A⁻¹ 0 (Fin.last n)=(-1)^n/A.det := by
  rw [Matrix.inv_def,Matrix.smul_apply,smul_eq_mul,
    Matrix.adjugate_fin_succ_eq_det_submatrix,Fin.succAbove_last,Fin.succAbove_zero,
    corner_minor_det A ht hu]
  simp only [Fin.val_last,Fin.val_zero,add_zero,mul_one,Ring.inverse_eq_inv]
  rw [div_eq_mul_inv,mul_comm]

theorem corner_solution_signed {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) (hd : A.det ≠ 0)
    (x : Fin (n+1) → ℝ) (hx : A.mulVec x=cornerRhs n) :
    x 0=(-1)^(n+1)/A.det := by
  have hinv : A⁻¹.mulVec (A.mulVec x)=x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.one_mulVec]
  rw [hx] at hinv
  have he := congrFun hinv 0
  have hsingle : A⁻¹.mulVec (cornerRhs n) 0=-A⁻¹ 0 (Fin.last n) := by
    simp [cornerRhs,Matrix.mulVec,dotProduct,Pi.single_apply]
  rw [hsingle,corner_inverse_entry A ht hu] at he
  rw [← he,pow_succ]
  ring

theorem corner_solution_even_dimension {n : ℕ} (hn : Odd n) (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) (hd : A.det ≠ 0)
    (x : Fin (n+1) → ℝ) (hx : A.mulVec x=cornerRhs n) :
    x 0=1/A.det := by
  rw [corner_solution_signed A ht hu hd x hx,pow_succ,hn.neg_one_pow]
  norm_num

#print axioms corner_solution_even_dimension
end IV04.Paper
