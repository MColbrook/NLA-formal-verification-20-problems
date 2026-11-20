module

/- Adapted from the real Frobenius and overlap lemmas in this project.
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0; see LICENSE.
Complex-field adaptation with Codex assistance. -/
public import NLA.RA09.ComplexDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.RA09.ComplexPaper

theorem frobeniusSquared_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ frobeniusSquared A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem frobeniusSquared_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSquared A = frobeniusNorm A ^ 2 := by
  rw [frobeniusNorm, Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Complex.normSq_eq_norm_sq, ← Real.sqrt_eq_rpow]
  exact (Real.sq_sqrt (frobeniusSquared_nonneg A)).symm

theorem frobeniusSquared_trace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    (frobeniusSquared A : ℂ) = Matrix.trace (A.conjTranspose * A) := by
  simp only [frobeniusSquared, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem unitary_star_mul {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : ComplexMatrix n).conjTranspose * (U : ComplexMatrix n) = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U

theorem unitary_mul_star {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (U : ComplexMatrix n) * (U : ComplexMatrix n).conjTranspose = 1 := by
  simpa only [Matrix.star_eq_conjTranspose] using U.2.2

theorem frobeniusSquared_mul_unitary_left {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin m) ℂ) :
    frobeniusSquared ((U : ComplexMatrix m) * A) = frobeniusSquared A := by
  apply Complex.ofReal_injective
  rw [frobeniusSquared_trace, frobeniusSquared_trace]
  have he : ((U : ComplexMatrix m) * A).conjTranspose * ((U : ComplexMatrix m) * A) =
      A.conjTranspose * ((U : ComplexMatrix m).conjTranspose * (U : ComplexMatrix m)) * A := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, unitary_star_mul, Matrix.mul_one]

theorem frobeniusSquared_mul_unitary_right {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    frobeniusSquared (A * (U : ComplexMatrix n)) = frobeniusSquared A := by
  apply Complex.ofReal_injective
  rw [frobeniusSquared_trace, frobeniusSquared_trace]
  have he : (A * (U : ComplexMatrix n)).conjTranspose * (A * (U : ComplexMatrix n)) =
      (U : ComplexMatrix n).conjTranspose * (A.conjTranspose * A) * (U : ComplexMatrix n) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, Matrix.trace_mul_cycle, unitary_mul_star, Matrix.one_mul]

theorem unitary_column_weights {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq ((U : ComplexMatrix n) i j) = 1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun M : ComplexMatrix n => M j j) (unitary_star_mul U)
  simpa only [Complex.ofReal_sum, Complex.ofReal_one, Complex.normSq_eq_conj_mul_self,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def] using h

theorem unitary_row_weights {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq ((U : ComplexMatrix n) i j) = 1 := by
  apply Complex.ofReal_injective
  have h := congrArg (fun M : ComplexMatrix n => M i i) (unitary_mul_star U)
  simpa only [Complex.ofReal_sum, Complex.ofReal_one, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply_eq, Complex.star_def, Complex.mul_conj] using h

theorem overlap_weights {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) :
    (∀ i j, 0 ≤ overlapWeights dA dB i j) ∧
    (∀ j, ∑ i, overlapWeights dA dB i j = 1) ∧
    (∀ i, ∑ j, overlapWeights dA dB i j = 1) :=
  ⟨fun _ _ => Complex.normSq_nonneg _, unitary_column_weights _, unitary_row_weights _⟩

#print axioms overlap_weights
end NLA.RA09.ComplexPaper
