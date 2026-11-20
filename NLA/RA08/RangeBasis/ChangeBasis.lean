module

public import NLA.RA08.PaperDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
namespace NLA.RA08.Paper.RangeBasis

theorem gram_basis_change {n l : ℕ} (A : RealMatrix n)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (T : Matrix (Fin l) (Fin l) ℝ) :
    (Ω * T).transpose * A * (Ω * T) =
      T.transpose * (Ω.transpose * A * Ω) * T := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem gram_basis_change_isUnit {n l : ℕ} (A : RealMatrix n)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (T : Matrix (Fin l) (Fin l) ℝ)
    (hG : IsUnit (Ω.transpose * A * Ω).det) (hT : IsUnit T.det) :
    IsUnit ((Ω * T).transpose * A * (Ω * T)).det := by
  rw [gram_basis_change, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact (hT.mul hG).mul hT

theorem nystrom_basis_change {n l : ℕ} (A : RealMatrix n)
    (Ω : Matrix (Fin n) (Fin l) ℝ) (T : Matrix (Fin l) (Fin l) ℝ)
    (hT : IsUnit T.det) :
    nystrom A (Ω * T) = nystrom A Ω := by
  have hTt : IsUnit T.transpose.det := by simpa only [Matrix.det_transpose] using hT
  rw [nystrom, nystrom, gram_basis_change, Matrix.transpose_mul,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left T _ hT]
  rw [Matrix.nonsing_inv_mul_cancel_left T.transpose _ hTt]

#print axioms gram_basis_change
#print axioms gram_basis_change_isUnit
#print axioms nystrom_basis_change
end NLA.RA08.Paper.RangeBasis
