module

public import NLA.MF05.PaperCyclicCharpoly

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
open Polynomial
namespace NLA.MF05.Paper.Cyclic

theorem perturbation_charpoly (n : ℕ) (δ : ℝ) :
    (perturbation n δ).charpoly = X^(n+1) - C δ := by
  cases n with
  | zero => simp [Matrix.charpoly, Matrix.det_unique, perturbation, weight]
  | succ n =>
    rw [Matrix.charpoly, Matrix.det_succ_column_zero]
    have hn : (0 : Fin (n+1+1)) ≠ Fin.last (n+1) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    rw [Finset.sum_eq_add_of_mem (0 : Fin (n+1+1)) (Fin.last (n+1))
      (Finset.mem_univ _) (Finset.mem_univ _) hn]
    · simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_last, Fin.succAbove_zero,
        Fin.succAbove_last, first_minor_det, last_minor_det]
      have h0 : (perturbation (n+1) δ).charmatrix 0 0 = X := by
        rw [charmatrix_entry]
        simp
      have hl : (perturbation (n+1) δ).charmatrix (Fin.last (n+1)) 0 = -C δ := by
        rw [charmatrix_entry]
        simp
      rw [h0, hl]
      have hs : (-1 : ℝ[X])^(n+1) * (-1)^(n+1) = 1 := by
        rw [← mul_pow]
        simp
      calc
        _ = X * X^(n+1) - C δ * ((-1)^(n+1) * (-1)^(n+1)) := by ring
        _ = X^(n+1+1) - C δ := by rw [hs]; ring
    · intro i _ hi
      have h0 : i.val ≠ 0 := by
        intro h
        exact hi.1 (Fin.ext h)
      have hl : i.val ≠ n+1 := by
        intro h
        exact hi.2 (Fin.ext h)
      have hz : (perturbation (n+1) δ).charmatrix i 0 = 0 := by
        rw [charmatrix_entry]
        simp [h0, hl]
      rw [hz, mul_zero, zero_mul]

#print axioms perturbation_charpoly
end NLA.MF05.Paper.Cyclic
