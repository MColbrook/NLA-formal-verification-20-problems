module

/- Adapted from Overlap.lean in this project.
Copyright (c) 2026 George Stepaniants. Apache 2.0; see LICENSE.
Complex-field adaptation with Codex assistance. -/
public import NLA.RA09.ComplexSpectral

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
namespace NLA.RA09.ComplexPaper

theorem spectralCombination_entry {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) (i j : Fin n) :
    spectralCombination d u i j = ∑ l,
      (d.unitary : ComplexMatrix n) i l * (u l : ℂ) * star ((d.unitary : ComplexMatrix n) j l) := by
  unfold spectralCombination
  rw [mul_apply]
  simp only [mul_diagonal, conjTranspose_apply]

theorem frobeniusSquared_sub_expansion {n : ℕ} (X Y : ComplexMatrix n)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    (frobeniusSquared (X-Y) : ℂ) = (frobeniusSquared X : ℂ) + (frobeniusSquared Y : ℂ) -
      2 * Matrix.trace (Y*X) := by
  rw [frobeniusSquared_trace, frobeniusSquared_trace, frobeniusSquared_trace]
  simp only [conjTranspose_sub, hX.eq, hY.eq, mul_sub, sub_mul, trace_sub]
  rw [trace_mul_comm X Y]
  ring

theorem spectralCombination_trace_product {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (u v : Fin n → ℝ) :
    Matrix.trace (spectralCombination dB v * spectralCombination dA u) =
      ((∑ j, v j * (∑ i, overlapWeights dA dB i j * u i)) : ℝ) := by
  let V : ComplexMatrix n := overlapUnitary dA dB
  have hin : (dB.unitary : ComplexMatrix n).conjTranspose * spectralCombination dA u *
      (dB.unitary : ComplexMatrix n) =
      V.conjTranspose * diagonal (fun i => (u i : ℂ)) * V := by
    simp only [V, spectralCombination, overlapUnitary, Submonoid.coe_mul, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, mul_assoc]
  calc
    _ = Matrix.trace ((dB.unitary : ComplexMatrix n) *
        (diagonal (fun j => (v j : ℂ)) *
          ((dB.unitary : ComplexMatrix n).conjTranspose * spectralCombination dA u))) := by
      congr 1
      simp only [spectralCombination, mul_assoc]
    _ = Matrix.trace ((diagonal (fun j => (v j : ℂ)) *
        ((dB.unitary : ComplexMatrix n).conjTranspose * spectralCombination dA u)) *
          (dB.unitary : ComplexMatrix n)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (diagonal (fun j => (v j : ℂ)) *
        (V.conjTranspose * diagonal (fun i => (u i : ℂ)) * V)) := by
      rw [← hin]
      congr 1
      simp only [mul_assoc]
    _ = _ := by
      simp only [Matrix.trace, Matrix.diag, Complex.ofReal_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [diagonal_mul]
      apply congrArg (fun z : ℂ => (v j : ℂ) * z)
      rw [mul_apply]
      simp only [mul_diagonal, conjTranspose_apply]
      apply Finset.sum_congr rfl
      intro i _
      simp only [overlapWeights, Complex.normSq_eq_conj_mul_self, Complex.star_def]
      change star ((overlapUnitary dA dB : ComplexMatrix n) i j) * (u i : ℂ) *
        (overlapUnitary dA dB : ComplexMatrix n) i j = _
      simp only [Complex.star_def]
      ring

theorem spectral_errors_general {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (u v : Fin n → ℝ) :
    frobeniusSquared (spectralCombination dA u - spectralCombination dB v) =
      (∑ i, u i ^ 2) + (∑ j, v j ^ 2) -
        2 * ∑ j, v j * (∑ i, overlapWeights dA dB i j * u i) := by
  apply Complex.ofReal_injective
  rw [frobeniusSquared_sub_expansion _ _ (spectralCombination_hermitian dA u)
    (spectralCombination_hermitian dB v), spectralCombination_frobenius,
    spectralCombination_frobenius, spectralCombination_trace_product]
  push_cast
  rfl

theorem overlap_error_expansions_proved {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (_hk : k ≤ n) :
    frobeniusSquared (A - truncation dB k) =
      (∑ i, dA.eigenvalues i ^ 2) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), dB.eigenvalues j ^ 2) -
      2 * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        dB.eigenvalues j * (∑ i, overlapWeights dA dB i j * dA.eigenvalues i) ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) =
      (∑ i, f (dA.eigenvalues i) ^ 2) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k), f (dB.eigenvalues j) ^ 2) -
      2 * ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
        f (dB.eigenvalues j) * (∑ i, overlapWeights dA dB i j * f (dA.eigenvalues i)) := by
  constructor
  · have h := spectral_errors_general dA dB dA.eigenvalues
      (fun j => if j.val < k then dB.eigenvalues j else 0)
    have hA : spectralCombination dA dA.eigenvalues = A := dA.reconstruct.symm
    rw [hA] at h
    simpa only [truncation, Finset.sum_filter, ite_pow, zero_pow (by decide : 2 ≠ 0),
      ite_mul, zero_mul] using h
  · rw [selected_cfc_eq, functionTruncation]
    have h := spectral_errors_general dA dB (fun i => f (dA.eigenvalues i))
      (fun j => if j.val < k then f (dB.eigenvalues j) else 0)
    simpa only [Finset.sum_filter, ite_pow, zero_pow (by decide : 2 ≠ 0),
      ite_mul, zero_mul] using h

theorem overlap_column_sum {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (j : Fin n) :
    ∑ i, overlapWeights dA dB i j = 1 := (overlap_weights dA dB).2.1 j

theorem overlap_row_sum {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (i : Fin n) :
    ∑ j, overlapWeights dA dB i j = 1 := (overlap_weights dA dB).2.2 i

#print axioms overlap_error_expansions_proved
end NLA.RA09.ComplexPaper
