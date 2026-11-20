module

/- Complex-field adaptation of the credited real overlap order proof. -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.
Actual PSD order gives every harmonic constraint on the overlap columns.
-/
public import NLA.RA09.ComplexOverlap
public import NLA.RA09.ComplexHarmonic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace NLA.RA09.ComplexPaper

theorem spectralCombination_single {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (j : Fin n) (b : ℝ) :
    spectralCombination d (Pi.single j b) =
      (b : ℂ) • outerSquare (fun i => (d.unitary : ComplexMatrix n) i j) := by
  ext i l
  rw [spectralCombination_entry]
  simp [Pi.single_apply, apply_ite, outerSquare, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, mul_comm, mul_assoc]

theorem selected_rankOne_le {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (j : Fin n) :
    (d.eigenvalues j : ℂ) • outerSquare (fun i => (d.unitary : ComplexMatrix n) i j) ≤ A := by
  have hs : spectralCombination d (Pi.single j (d.eigenvalues j)) ≤
      spectralCombination d d.eigenvalues := by
    apply spectralCombination_le
    intro i
    by_cases hi : i = j
    · subst i
      simp
    · simp [hi, d.nonnegative i]
  rw [spectralCombination_single] at hs
  exact hs.trans_eq d.reconstruct.symm

theorem outerSquare_conjugate {n : ℕ} (Q : ComplexMatrix n) (v : Fin n → ℂ) :
    Q.conjTranspose * outerSquare v * Q = outerSquare (Q.conjTranspose *ᵥ v) := by
  change Q.conjTranspose * vecMulVec v (star v) * Q =
    vecMulVec (Q.conjTranspose *ᵥ v) (star (Q.conjTranspose *ᵥ v))
  rw [mul_vecMulVec, vecMulVec_mul]
  congr 1
  ext i
  simp [vecMul, mulVec, dotProduct, conjTranspose_apply, star_mul, mul_comm]

theorem overlap_rankOne_order {n : ℕ} {A Ahat : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (j : Fin n) :
    (diagonal (fun i => (dA.eigenvalues i : ℂ)) - (dHat.eigenvalues j : ℂ) •
      outerSquare (fun i => (overlapUnitary dA dHat : ComplexMatrix n) i j)).PosSemidef := by
  have hless := (selected_rankOne_le dHat j).trans horder
  have hp := (sub_nonneg.mpr hless).posSemidef
  have hc := hp.conjTranspose_mul_mul_same (dA.unitary : ComplexMatrix n)
  have hA : (dA.unitary : ComplexMatrix n).conjTranspose * A * (dA.unitary : ComplexMatrix n) =
      diagonal (fun i => (dA.eigenvalues i : ℂ)) := by
    exact (congrArg (fun M : ComplexMatrix n =>
      (dA.unitary : ComplexMatrix n).conjTranspose * M * (dA.unitary : ComplexMatrix n))
        dA.reconstruct).trans (spectralCombination_conjugate dA dA.eigenvalues)
  have hv : (dA.unitary : ComplexMatrix n).conjTranspose *ᵥ
      (fun i => (dHat.unitary : ComplexMatrix n) i j) =
        (fun i => (overlapUnitary dA dHat : ComplexMatrix n) i j) := by
    funext i
    simp only [overlapUnitary, Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose, mul_apply, mulVec, dotProduct, conjTranspose_apply]
  have he : (dA.unitary : ComplexMatrix n).conjTranspose *
      (A - (dHat.eigenvalues j : ℂ) • outerSquare (fun i => (dHat.unitary : ComplexMatrix n) i j)) *
        (dA.unitary : ComplexMatrix n) =
      diagonal (fun i => (dA.eigenvalues i : ℂ)) - (dHat.eigenvalues j : ℂ) • outerSquare (fun i => (overlapUnitary dA dHat : ComplexMatrix n) i j) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, hA, outerSquare_conjugate, hv]
  simpa only [he] using hc

theorem overlap_semantics_proved {n : ℕ} {A Ahat : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat)
    (horder : Ahat ≤ A) (k : ℕ) (_hk : k ≤ n) :
    (∀ i j, 0 ≤ overlapWeights dA dHat i j) ∧
    (∀ j, ∑ i, overlapWeights dA dHat i j = 1) ∧
    (∀ i, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k),
      overlapWeights dA dHat i j ≤ 1) ∧
    (∀ j : Fin n, 0 < dHat.eigenvalues j →
      (∀ i, dA.eigenvalues i = 0 → overlapWeights dA dHat i j = 0) ∧
      dHat.eigenvalues j *
        (∑ i, overlapWeights dA dHat i j / dA.eigenvalues i) ≤ 1) := by
  refine ⟨(overlap_weights dA dHat).1, overlap_column_sum dA dHat, ?_, ?_⟩
  · intro i
    calc
      _ ≤ ∑ j, overlapWeights dA dHat i j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => (overlap_weights dA dHat).1 i j)
      _ = 1 := overlap_row_sum dA dHat i
  · intro j hj
    have h := harmonic_constraint_proved dA.eigenvalues
      (fun i => (overlapUnitary dA dHat : ComplexMatrix n) i j) (dHat.eigenvalues j)
      dA.nonnegative hj (overlap_rankOne_order dA dHat horder j)
    refine ⟨?_, h.2⟩
    intro i hi
    simp only [overlapWeights, h.1 i hi, map_zero]

#print axioms overlap_semantics_proved

end NLA.RA09.ComplexPaper
