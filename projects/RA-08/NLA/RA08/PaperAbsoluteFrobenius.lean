module

public import NLA.RA08.PaperFrobeniusCFC

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix
namespace NLA.RA08.Paper

open scoped Matrix.Norms.Frobenius in
theorem frobeniusNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusNorm A := norm_nonneg A

theorem frobeniusSquared_cfc_nonexpansive {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x y, |f x-f y| ≤ |x-y|) :
    frobeniusSquared (functionalCalculus f A-functionalCalculus f B) ≤ frobeniusSquared (A-B) := by
  have hidA : functionalCalculus id A = A := cfc_id' ℝ A hA
  have hidB : functionalCalculus id B = B := cfc_id' ℝ B hB
  have hi := frobeniusSquared_cfc_difference A B hA hB id id
  simp only [hidA,hidB,id_eq] at hi
  rw [frobeniusSquared_cfc_difference A B hA hB f f,hi]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hs := mul_self_le_mul_self (abs_nonneg (f (hA.eigenvalues i)-f (hB.eigenvalues j)))
    (hf (hA.eigenvalues i) (hB.eigenvalues j))
  have hh : (f (hA.eigenvalues i)-f (hB.eigenvalues j))^2 ≤
      (hA.eigenvalues i-hB.eigenvalues j)^2 := by simpa only [← pow_two,sq_abs] using hs
  exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

theorem frobeniusNorm_cfc_nonexpansive {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ x y, |f x-f y| ≤ |x-y|) :
    frobeniusNorm (functionalCalculus f A-functionalCalculus f B) ≤ frobeniusNorm (A-B) := by
  have hs := frobeniusSquared_cfc_nonexpansive A B hA hB f hf
  rw [frobeniusSquared_norm,frobeniusSquared_norm] at hs
  exact (sq_le_sq₀ (frobeniusNorm_nonneg _) (frobeniusNorm_nonneg _)).mp hs

theorem matrixAbsolute_frobenius_nonexpansive {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    frobeniusNorm (matrixAbsolute A-matrixAbsolute B) ≤ frobeniusNorm (A-B) := by
  apply frobeniusNorm_cfc_nonexpansive A B hA hB abs
  intro x y
  exact abs_abs_sub_abs_le_abs_sub x y

#print axioms matrixAbsolute_frobenius_nonexpansive
end NLA.RA08.Paper
