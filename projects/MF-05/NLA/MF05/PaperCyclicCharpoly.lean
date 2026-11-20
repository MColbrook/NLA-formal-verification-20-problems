module

public import NLA.MF05.PaperCyclicNorm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open Polynomial
namespace NLA.MF05.Paper.Cyclic

theorem charmatrix_entry (n : ℕ) (δ : ℝ) (i j : Fin (n+1)) :
    (perturbation n δ).charmatrix i j =
      (if i.val = j.val then X else 0) - (if i.val+1 = j.val then 1 else 0) -
      (if i.val = n ∧ j.val = 0 then C δ else 0) := by
  rw [Matrix.charmatrix_apply, perturbation_literal]
  simp only [Matrix.diagonal_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    shift, corner, Matrix.single, Matrix.of_apply, map_add, map_mul]
  have he : i = j ↔ i.val = j.val := Fin.ext_iff
  have hc : (Fin.last n = i ∧ (0 : Fin (n+1)) = j) ↔ i.val = n ∧ j.val = 0 := by
    constructor
    · rintro ⟨rfl, rfl⟩
      simp
    · rintro ⟨hi, hj⟩
      exact ⟨(Fin.ext hi).symm, (Fin.ext hj).symm⟩
  simp only [he, hc, apply_ite, map_zero, map_one, mul_ite, mul_one, mul_zero]
  split_ifs <;> ring

theorem first_minor_det (n : ℕ) (δ : ℝ) :
    ((perturbation n δ).charmatrix.submatrix Fin.succ Fin.succ).det = X^n := by
  let M := (perturbation n δ).charmatrix.submatrix Fin.succ Fin.succ
  have hu : M.IsUpperTriangular := by
    intro i j hij
    change j.val < i.val at hij
    change (perturbation n δ).charmatrix i.succ j.succ = 0
    rw [charmatrix_entry]
    have h1 : i.val + 1 ≠ j.val + 1 := by omega
    have h2 : i.val + 1 + 1 ≠ j.val + 1 := by omega
    have h3 : i.val ≠ j.val := by omega
    have h4 : i.val + 1 ≠ j.val := by omega
    simp [h1, h2, h3, h4]
  have hd (i : Fin n) : M i i = X := by
    change (perturbation n δ).charmatrix i.succ i.succ = X
    rw [charmatrix_entry]
    simp
  change M.det = _
  rw [Matrix.det_of_isUpperTriangular hu]
  simp [hd]

theorem last_minor_det (n : ℕ) (δ : ℝ) :
    ((perturbation n δ).charmatrix.submatrix Fin.castSucc Fin.succ).det = (-1)^n := by
  let M := (perturbation n δ).charmatrix.submatrix Fin.castSucc Fin.succ
  have hl : M.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    change (perturbation n δ).charmatrix i.castSucc j.succ = 0
    rw [charmatrix_entry]
    have h1 : i.val ≠ j.val+1 := by omega
    have h2 : i.val+1 ≠ j.val+1 := by omega
    have h3 : i.val ≠ j.val := by omega
    simp [h1, h2, h3]
  have hd (i : Fin n) : M i i = -1 := by
    change (perturbation n δ).charmatrix i.castSucc i.succ = -1
    rw [charmatrix_entry]
    simp
  change M.det = _
  rw [Matrix.det_of_isLowerTriangular M hl]
  simp [hd]

end NLA.MF05.Paper.Cyclic
