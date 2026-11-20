module

public import NLA.MF05.PaperCyclicNorm

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF05.Paper.Cyclic

theorem perturbation_mul (n : ℕ) (δ : ℝ) (B : RealSquare (n+1)) (i j : Fin (n+1)) :
    (perturbation n δ * B) i j = weight n δ i * B (finRotate (n+1) i) j := by
  simp [Matrix.mul_apply, perturbation, ite_mul]

theorem shift_mul (n : ℕ) (B : RealSquare (n+1)) (i j : Fin (n+1)) :
    (shift n * B) i j = weight n 0 i * B (finRotate (n+1) i) j := by
  rw [← perturbation_zero]
  exact perturbation_mul n 0 B i j

theorem shift_pow (n k : ℕ) (i j : Fin (n+1)) :
    (shift n ^ k) i j = if i.val + k = j.val then 1 else 0 := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ k ih =>
    rw [pow_succ', shift_mul, ih]
    by_cases hi : i = Fin.last n
    · subst i
      have hj : ¬ n + (k+1) = j.val := by omega
      simp [weight, hj]
    · have hlt : i.val < n := by
        have hv : i.val ≠ n := by
          intro h
          exact hi (Fin.ext h)
        omega
      have hr : finRotate (n+1) i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hlt
      simp [weight, hi, hr, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem shift_nilpotent (n : ℕ) : shift n ^ (n+1) = 0 := by
  ext i j
  rw [shift_pow]
  have h : ¬ i.val + (n+1) = j.val := by omega
  simp [h]

#print axioms shift_nilpotent
end NLA.MF05.Paper.Cyclic
