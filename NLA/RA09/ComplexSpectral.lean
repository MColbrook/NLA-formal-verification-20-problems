module

/- Adapted from Spectral.lean in this project.
Copyright (c) 2026 George Stepaniants. Apache 2.0; see LICENSE.
Complex-field adaptation with Codex assistance. -/
public import NLA.RA09.ComplexFrobenius
public import NLA.RA09.ComplexSpectralCFC
public import NLA.RA09.Spectral

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
namespace NLA.RA09.ComplexPaper

theorem spectralCombination_hermitian {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) :
    (spectralCombination d u).IsHermitian := by
  change (spectralCombination d u).conjTranspose = spectralCombination d u
  simp [spectralCombination, conjTranspose_mul, diagonal_conjTranspose,
    Pi.star_def, Complex.star_def, mul_assoc]

theorem spectralCombination_sub {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u v : Fin n → ℝ) :
    spectralCombination d u - spectralCombination d v =
      spectralCombination d (fun i => u i - v i) := by
  have hd : diagonal (fun i => (u i : ℂ) - (v i : ℂ)) =
      diagonal (fun i => (u i : ℂ)) - diagonal (fun i => (v i : ℂ)) :=
    (Matrix.diagonal_sub (fun i => (u i : ℂ)) (fun i => (v i : ℂ))).symm
  simp only [spectralCombination, Complex.ofReal_sub, hd, mul_sub, sub_mul]

theorem spectralCombination_posSemidef {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (spectralCombination d u).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal (fun i => by simpa using hu i)).mul_mul_conjTranspose_same _

theorem spectralCombination_le {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u v : Fin n → ℝ) (huv : ∀ i, u i ≤ v i) :
    spectralCombination d u ≤ spectralCombination d v := by
  apply sub_nonneg.mp
  rw [spectralCombination_sub]
  exact (spectralCombination_posSemidef d _ (fun i => sub_nonneg.mpr (huv i))).nonneg

theorem spectralCombination_conjugate {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) :
    (d.unitary : ComplexMatrix n).conjTranspose * spectralCombination d u *
      (d.unitary : ComplexMatrix n) = diagonal (fun i => (u i : ℂ)) := by
  calc
    _ = ((d.unitary : ComplexMatrix n).conjTranspose * (d.unitary : ComplexMatrix n)) *
        diagonal (fun i => (u i : ℂ)) *
        ((d.unitary : ComplexMatrix n).conjTranspose * (d.unitary : ComplexMatrix n)) := by
      simp only [spectralCombination, mul_assoc]
    _ = _ := by rw [unitary_star_mul]; simp only [one_mul, mul_one]

theorem spectralCombination_injective {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) : Function.Injective (spectralCombination d) := by
  intro u v huv
  have he := congrArg (fun M : ComplexMatrix n =>
    (d.unitary : ComplexMatrix n).conjTranspose * M * (d.unitary : ComplexMatrix n)) huv
  rw [spectralCombination_conjugate, spectralCombination_conjugate] at he
  funext i
  apply Complex.ofReal_injective
  simpa only [diagonal_apply_eq] using congrArg (fun M : ComplexMatrix n => M i i) he

theorem spectralCombination_frobenius {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) :
    frobeniusSquared (spectralCombination d u) = ∑ i, u i ^ 2 := by
  have hs : (d.unitary : ComplexMatrix n).conjTranspose =
      ((star d.unitary : Matrix.unitaryGroup (Fin n) ℂ) : ComplexMatrix n) := by
    simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose]
  unfold spectralCombination
  rw [hs, frobeniusSquared_mul_unitary_right, frobeniusSquared_mul_unitary_left]
  simp [frobeniusSquared, Matrix.diagonal_apply, apply_ite, Complex.normSq_ofReal, pow_two]

theorem truncation_semantics_proved {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (_hk : k ≤ n) (f : ℝ → ℝ) :
    (truncation d k).PosSemidef ∧ truncation d k ≤ A ∧
    frobeniusSquared (A - truncation d k) = spectralTail d k ∧
    frobeniusSquared (functionalCalculus f A - functionTruncation d f k) = functionTail d f k ∧
    (truncation d k = A ↔ ∀ i : Fin n, k ≤ i.val → d.eigenvalues i = 0) := by
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply spectralCombination_posSemidef
    intro i
    split_ifs
    · exact d.nonnegative i
    · exact le_rfl
  · apply LE.le.trans_eq (b := spectralCombination d d.eigenvalues) ?_ hA.symm
    apply spectralCombination_le
    intro i
    split_ifs
    · exact le_rfl
    · exact d.nonnegative i
  · calc
      _ = frobeniusSquared (spectralCombination d d.eigenvalues - truncation d k) := by rw [← hA]
      _ = _ := by
        rw [truncation, spectralCombination_sub, spectralCombination_frobenius]
        exact NLA.RA09.tail_square_sum d.eigenvalues k
  · rw [selected_cfc_eq, functionTruncation, spectralCombination_sub, spectralCombination_frobenius]
    exact NLA.RA09.tail_square_sum _ k
  · constructor
    · intro h i hi
      have hv := congrFun (spectralCombination_injective d (h.trans hA)) i
      simpa only [Nat.not_lt.mpr hi, ↓reduceIte] using hv.symm
    · intro h
      apply Eq.trans (b := spectralCombination d d.eigenvalues) ?_ hA.symm
      apply congrArg (spectralCombination d)
      funext i
      by_cases hi : i.val < k
      · simp [hi]
      · simp [hi, h i (Nat.le_of_not_gt hi)]

#print axioms truncation_semantics_proved
end NLA.RA09.ComplexPaper
