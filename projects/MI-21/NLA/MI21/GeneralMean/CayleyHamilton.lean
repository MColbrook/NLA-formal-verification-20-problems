module

public import NLA.MI21.Proof
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI21.GeneralMean

theorem two_by_two_cayley_hamilton (M : Mat 2) :
    M * M + M.det • (1 : Mat 2) = M.trace • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace,
      Matrix.smul_apply] <;> ring

theorem scaled_riccati_two_by_two (C D K : Mat 2) (d : ℂ)
    (hCK : C * K = 1) (hKC : K * C = 1) (hd : d ^ 2 = (K * D).det) :
    (D + d • C) * K * (D + d • C) = ((K * D).trace + 2 * d) • D := by
  have hch := congrArg (fun Z : Mat 2 => C * Z) (two_by_two_cayley_hamilton (K * D))
  simp only [mul_add, mul_smul_comm, mul_one, ← Matrix.mul_assoc, hCK, one_mul] at hch
  have hDKC : D * K * C = D := by rw [Matrix.mul_assoc, hKC, mul_one]
  have hCKD : C * K * D = D := by rw [hCK, one_mul]
  have hCKC : C * K * C = C := by rw [hCK, one_mul]
  calc
    (D + d • C) * K * (D + d • C) =
        (D * K * D + (d * d) • C) + (d + d) • D := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
        hDKC, hCKD, hCKC, add_smul]
      abel
    _ = ((K * D).trace + 2 * d) • D := by
      rw [← pow_two d, hd, hch, ← add_smul]
      congr 1
      ring

#print axioms two_by_two_cayley_hamilton
#print axioms scaled_riccati_two_by_two
end NLA.MI21.GeneralMean
