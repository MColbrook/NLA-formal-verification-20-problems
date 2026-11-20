module

/- Adapted from the credited MF07 maximal-determinant/SVD proof by
George Stepaniants, using Matthew J. Colbrook's mathematical argument.
Real-field generalization and paper interface developed with Codex. -/
public import NLA.MF05.PaperNormBounds

@[expose] public section

set_option autoImplicit false
open NLA.MF07
noncomputable section
namespace NLA.MF05.Paper

theorem rounded_of_norm {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (L : ℝ) (hML : ∀ A ∈ M, spectralNorm A ≤ L) (a : ℝ)
    (v : EuclideanVector d → ℝ) (c : ℝ) (hc : 1 ≤ c) (hv : IsComplexNorm v)
    (hbound : ∀ x, ‖x‖ ≤ v x ∧ v x ≤ c*‖x‖)
    (hgen : ∀ A ∈ M, ∀ x, v (applyMatrix A x) ≤ a*v x) :
    ∃ (Q : Square d) (σ : Fin d → ℝ) (w : EuclideanVector d → ℝ),
      IsUnitary Q ∧ Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsComplexNorm w ∧
      (∀ x, ‖x‖ ≤ w x ∧ w x ≤ (d : ℝ)*‖x‖) ∧
      (∀ A ∈ M, ∀ x, w (applyMatrix (rotatedGenerator Q σ A) x) ≤ a*w x) ∧
      ∀ A ∈ M, ∀ i j, ‖rotatedGenerator Q σ A i j‖ ≤ L*σ j/σ i := by
  obtain ⟨T, hT, hcoords⟩ := exists_auerbach_coordinates hv c hc hbound
  obtain ⟨Q, R, σ, hQ, hR, hσ, hmono, hTR⟩ := exists_singular_coordinates T hT
  let P := Q * diagonalWeights σ
  let U := inverseDiagonalWeights σ * Q.conjTranspose
  let r := Real.sqrt (d : ℝ)
  let w : EuclideanVector d → ℝ := fun x => r * v (applyMatrix P x)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hrpos : 0 < r := Real.sqrt_pos.mpr hdpos
  have hrsq : r * r = (d : ℝ) := Real.mul_self_sqrt hdpos.le
  have hinv := diagonal_inverse σ (fun i => (hσ i).ne')
  have hUP : U * P = 1 := by
    calc
      U * P = inverseDiagonalWeights σ * (Q.conjTranspose * Q) * diagonalWeights σ := by
        dsimp [U, P]
        noncomm_ring
      _ = 1 := by rw [hQ.1, mul_one, hinv.2]
  have hPU : P * U = 1 := by
    calc
      P * U = Q * (diagonalWeights σ * inverseDiagonalWeights σ) * Q.conjTranspose := by
        dsimp [P, U]
        noncomm_ring
      _ = 1 := by rw [hinv.1, mul_one, hQ.2]
  have hw : IsComplexNorm w := complexNorm_transport hv P U hUP r hrpos
  have hwb : ∀ x, ‖x‖ ≤ w x ∧ w x ≤ (d : ℝ) * ‖x‖ := by
    intro x
    have hb := hcoords (applyMatrix R x)
    have he : applyMatrix P x = applyMatrix T (applyMatrix R x) := by
      rw [← applyMatrix_mul, hTR]
    have hn := norm_applyMatrix_unitary hd hR x
    refine ⟨?_, ?_⟩
    · simpa only [w, r, he, hn] using hb.1
    · calc
        w x = r * v (applyMatrix T (applyMatrix R x)) := by
          dsimp only [w]
          rw [he]
        _ ≤ r * (r * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _ hrpos.le
          simpa only [r, hn] using hb.2
        _ = (d : ℝ) * ‖x‖ := by rw [← mul_assoc, hrsq]
  have hconj : ∀ A, P * rotatedGenerator Q σ A = A * P := by
    intro A
    have he : rotatedGenerator Q σ A = U * A * P := by
      dsimp [rotatedGenerator, U, P]
      noncomm_ring
    rw [he]
    calc
      P * (U * A * P) = (P * U) * (A * P) := by noncomm_ring
      _ = A * P := by rw [hPU, one_mul]
  refine ⟨Q, σ, w, hQ, hmono, hσ, hw, hwb, ?_, ?_⟩
  · intro A hA x
    calc
      w (applyMatrix (rotatedGenerator Q σ A) x) =
          r * v (applyMatrix A (applyMatrix P x)) := by
        dsimp only [w]
        rw [← applyMatrix_mul, hconj, applyMatrix_mul]
      _ ≤ r * (a * v (applyMatrix P x)) :=
        mul_le_mul_of_nonneg_left (hgen A hA _) hrpos.le
      _ = a * w x := by dsimp [w]; ring
  · intro A hA i j
    exact rotatedGenerator_entry_bound hd hQ σ hσ A L (hML A hA) i j

#print axioms rounded_of_norm
end NLA.MF05.Paper
