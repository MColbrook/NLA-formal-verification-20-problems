module

/- The elementary trace/orthogonal invariance arguments adapt the credited
RA09/Frobenius.lean formalization by George Stepaniants (Apache 2.0).
The general Hermitian CFC rotation argument is developed here for the printed
threshold derivative, with Codex assistance. No PSD spectral oracle is assumed. -/
public import NLA.RA08.PaperDerivativeDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix
namespace NLA.RA08.Paper

theorem frobeniusSquared_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ frobeniusSquared A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem frobeniusSquared_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusSquared A = (A.transpose*A).trace := by
  simp only [frobeniusSquared,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,pow_two]
  exact Finset.sum_comm

theorem frobeniusSquared_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusSquared A = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm,Matrix.frobenius_norm_def]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (frobeniusSquared_nonneg A)).symm

theorem real_unitary_transpose_mul {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) :
    (U : RealMatrix n).transpose*(U : RealMatrix n)=1 := by
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
    using Unitary.coe_star_mul_self U

theorem real_unitary_mul_transpose {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) :
    (U : RealMatrix n)*(U : RealMatrix n).transpose=1 := by
  simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
    using Unitary.coe_mul_star_self U

theorem frobeniusSquared_unitary_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin m) ℝ) :
    frobeniusSquared ((U : RealMatrix m)*A)=frobeniusSquared A := by
  rw [frobeniusSquared_trace,frobeniusSquared_trace]
  have he : ((U : RealMatrix m)*A).transpose*((U : RealMatrix m)*A) =
      A.transpose*((U : RealMatrix m).transpose*(U : RealMatrix m))*A := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  rw [he,real_unitary_transpose_mul,Matrix.mul_one]

theorem frobeniusSquared_unitary_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    frobeniusSquared (A*(U : RealMatrix n))=frobeniusSquared A := by
  rw [frobeniusSquared_trace,frobeniusSquared_trace]
  have he : (A*(U : RealMatrix n)).transpose*(A*(U : RealMatrix n)) =
      (U : RealMatrix n).transpose*(A.transpose*A)*(U : RealMatrix n) := by
    simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  rw [he,Matrix.trace_mul_cycle,real_unitary_mul_transpose,Matrix.one_mul]

theorem frobeniusSquared_rotated {n : ℕ} (A : RealMatrix n)
    (U V : Matrix.unitaryGroup (Fin n) ℝ) :
    frobeniusSquared ((U : RealMatrix n).transpose*A*(V : RealMatrix n))=frobeniusSquared A := by
  have hu : (U : RealMatrix n).transpose=(star U : Matrix.unitaryGroup (Fin n) ℝ) := by
    simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hu,frobeniusSquared_unitary_right,frobeniusSquared_unitary_left]

theorem real_cfc_spectral_form {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    functionalCalculus f A = (hA.eigenvectorUnitary : RealMatrix n)*
      Matrix.diagonal (fun i => f (hA.eigenvalues i))*(hA.eigenvectorUnitary : RealMatrix n).transpose := by
  rw [functionalCalculus,hA.cfc_eq]
  simp [Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply,Unitary.coe_star,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def]

theorem rotated_diagonal_difference {n : ℕ} (U V : Matrix.unitaryGroup (Fin n) ℝ)
    (a b : Fin n → ℝ) :
    (U : RealMatrix n).transpose*((U : RealMatrix n)*Matrix.diagonal a*(U : RealMatrix n).transpose -
      (V : RealMatrix n)*Matrix.diagonal b*(V : RealMatrix n).transpose)*(V : RealMatrix n) =
      Matrix.diagonal a*((U : RealMatrix n).transpose*(V : RealMatrix n)) -
        ((U : RealMatrix n).transpose*(V : RealMatrix n))*Matrix.diagonal b := by
  rw [Matrix.mul_sub,Matrix.sub_mul]
  congr 1
  · calc
      _ = ((U : RealMatrix n).transpose*(U : RealMatrix n))*Matrix.diagonal a*
          ((U : RealMatrix n).transpose*(V : RealMatrix n)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [real_unitary_transpose_mul,Matrix.one_mul]
  · calc
      _ = ((U : RealMatrix n).transpose*(V : RealMatrix n))*Matrix.diagonal b*
          ((V : RealMatrix n).transpose*(V : RealMatrix n)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [real_unitary_transpose_mul,Matrix.mul_one]

theorem frobeniusSquared_cfc_difference {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    frobeniusSquared (functionalCalculus f A-functionalCalculus g B) =
      ∑ i, ∑ j, (f (hA.eigenvalues i)-g (hB.eigenvalues j))^2 *
        (((hA.eigenvectorUnitary : RealMatrix n).transpose*(hB.eigenvectorUnitary : RealMatrix n)) i j)^2 := by
  rw [← frobeniusSquared_rotated _ hA.eigenvectorUnitary hB.eigenvectorUnitary]
  rw [real_cfc_spectral_form A hA f,real_cfc_spectral_form B hB g,rotated_diagonal_difference]
  simp only [frobeniusSquared,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

#print axioms frobeniusSquared_cfc_difference
end NLA.RA08.Paper
