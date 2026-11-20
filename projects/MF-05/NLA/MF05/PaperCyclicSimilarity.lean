module

public import NLA.MF05.PaperCyclicNorm

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF05.Paper.Cyclic

def scaling (n : ℕ) (r : ℝ) : RealSquare (n+1) := Matrix.diagonal (fun i => r^i.val)
def unscaling (n : ℕ) (r : ℝ) : RealSquare (n+1) := Matrix.diagonal (fun i => (r^i.val)⁻¹)

theorem scaling_inverse (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    scaling n r * unscaling n r = 1 ∧ unscaling n r * scaling n r = 1 := by
  constructor <;> simp [scaling, unscaling, Matrix.diagonal_mul_diagonal, pow_ne_zero _ hr]

def scalingUnit (n : ℕ) (r : ℝ) (hr : r ≠ 0) : (RealSquare (n+1))ˣ where
  val := scaling n r
  inv := unscaling n r
  val_inv := (scaling_inverse n r hr).1
  inv_val := (scaling_inverse n r hr).2

theorem scaled_perturbation (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    unscaling n r * perturbation n (r^(n+1)) * scaling n r = r • perturbation n 1 := by
  ext i j
  simp only [unscaling, scaling, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, smul_eq_mul]
  by_cases hj : j = finRotate (n+1) i
  · subst j
    by_cases hi : i = Fin.last n
    · subst i
      simp [perturbation, weight, finRotate_last, pow_succ, hr, pow_ne_zero _ hr,
        mul_assoc, mul_comm, mul_left_comm]
    · have hlt : i.val < n := by
        have hv : i.val ≠ n := by
          intro h
          exact hi (Fin.ext h)
        omega
      have hrot : finRotate (n+1) i = ⟨i.val+1, by omega⟩ := finRotate_of_lt hlt
      simp [perturbation, weight, hi, hrot, pow_succ, pow_ne_zero _ hr,
        mul_assoc, mul_comm, mul_left_comm]
  · simp only [perturbation, if_neg hj, mul_zero, zero_mul]

theorem perturbation_conjugate (n : ℕ) (r : ℝ) (hr : r ≠ 0) :
    perturbation n (r^(n+1)) =
      scaling n r * (r • perturbation n 1) * unscaling n r := by
  rw [← scaled_perturbation n r hr]
  have hi := scaling_inverse n r hr
  calc
    _ = (scaling n r * unscaling n r) * perturbation n (r^(n+1)) *
        (scaling n r * unscaling n r) := by rw [hi.1]; simp
    _ = _ := by noncomm_ring

theorem perturbation_power_conjugate (n k : ℕ) (r : ℝ) (hr : r ≠ 0) :
    perturbation n (r^(n+1)) ^ k =
      scaling n r * (r • perturbation n 1)^k * unscaling n r := by
  rw [perturbation_conjugate n r hr]
  exact Units.conj_pow (scalingUnit n r hr) (r • perturbation n 1) k

#print axioms perturbation_power_conjugate
end NLA.MF05.Paper.Cyclic
