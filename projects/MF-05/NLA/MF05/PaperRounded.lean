module

public import NLA.MF05.PaperRoundedDefinitions
public import NLA.MF05.PaperRoundedComplex
public import NLA.MF05.RealGeometry.RoundedGeneral

@[expose] public section

set_option autoImplicit false
open NLA.MF07
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MF05.Paper

theorem complex_rounded_extremal_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (a : ℝ) (ha : jointSpectralRadius M < a) :
    ∃ (Q : Square d) (σ : Fin d → ℝ) (w : EuclideanVector d → ℝ),
      Q.conjTranspose*Q = 1 ∧ Q*Q.conjTranspose = 1 ∧
      Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsComplexNorm w ∧
      (∀ z, ‖z‖ ≤ w z ∧ w z ≤ (d : ℝ)*‖z‖) ∧
      (∀ A ∈ M, inducedNorm w (applyMatrix (complexRotated Q σ A)) ≤ a) ∧
      ∀ A ∈ M, ∀ i j, ‖complexRotated Q σ A i j‖ ≤ L*σ j/σ i := by
  let ε := min (a-jointSpectralRadius M) (2*(d : ℝ)^2*L)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hε : 0 < ε := lt_min (sub_pos.mpr ha) (by positivity)
  have hεL : ε ≤ 2*(d : ℝ)^2*L := min_le_right _ _
  obtain ⟨v, hv, hb, hg⟩ := complex_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL
  have hc : 1 ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) :=
    comparisonFactor_ge_one d hd _ ((one_le_div hε).mpr hεL)
  have hrate : jointSpectralRadius M+ε ≤ a := by
    have h := min_le_left (a-jointSpectralRadius M) (2*(d : ℝ)^2*L)
    dsimp [ε]
    linarith
  obtain ⟨Q, σ, w, hQ, hmono, hσ, hw, hwb, hwg, hentry⟩ :=
    rounded_of_norm hd M L hML a v _ hc hv hb (fun A hA x =>
      (hg A hA x).trans (mul_le_mul_of_nonneg_right hrate (hv.1 x)))
  have he : ∀ A, complexRotated Q σ A = rotatedGenerator Q σ A := by
    intro A
    unfold complexRotated
    rw [Matrix.inv_eq_left_inv (diagonal_inverse σ (fun i => (hσ i).ne')).2]
    rfl
  let e : EuclideanVector d := PiLp.single 2 (⟨0, by omega⟩ : Fin d) (1 : ℂ)
  have he0 : e ≠ 0 := by simp [e]
  refine ⟨Q, σ, w, hQ.1, hQ.2, hmono, hσ, hw, hwb, ?_, ?_⟩
  · intro A hA
    rw [he]
    exact inducedNorm_le w _ (fun x => (hwb x).1) a (hwg A hA) e he0
  · intro A hA i j
    rw [he]
    exact hentry A hA i j

theorem real_rounded_extremal_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (a : ℝ) (ha : realRadius M < a) :
    ∃ (Q : RealSquare d) (σ : Fin d → ℝ) (w : RealVector d → ℝ),
      Q.transpose*Q = 1 ∧ Q*Q.transpose = 1 ∧
      Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsRealNorm w ∧
      (∀ z, ‖z‖ ≤ w z ∧ w z ≤ (d : ℝ)*‖z‖) ∧
      (∀ A ∈ M, inducedNorm w (Matrix.toEuclideanCLM (𝕜:=ℝ) (realRotated Q σ A)) ≤ a) ∧
      ∀ A ∈ M, ∀ i j, ‖realRotated Q σ A i j‖ ≤ L*σ j/σ i := by
  let ε := min (a-realRadius M) (2*(d : ℝ)^2*L)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hε : 0 < ε := lt_min (sub_pos.mpr ha) (by positivity)
  have hεL : ε ≤ 2*(d : ℝ)^2*L := min_le_right _ _
  obtain ⟨v, hv, hb, hg⟩ := real_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL
  have hc : 1 ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) :=
    comparisonFactor_ge_one d hd _ ((one_le_div hε).mpr hεL)
  have hrate : realRadius M+ε ≤ a := by
    have h := min_le_left (a-realRadius M) (2*(d : ℝ)^2*L)
    dsimp [ε]
    linarith
  obtain ⟨Q, σ, w, hQ, hmono, hσ, hw, hwb, hwg, hentry⟩ :=
    RealGeometry.rounded_of_norm hd M L hML a v _ hc hv hb (fun A hA x =>
      (hg A hA x).trans (mul_le_mul_of_nonneg_right hrate (hv.1 x)))
  have he : ∀ A, realRotated Q σ A = RealGeometry.rotatedGenerator Q σ A := by
    intro A
    unfold realRotated
    change (RealGeometry.diagonalWeights σ)⁻¹ * Q.transpose * A * Q *
      RealGeometry.diagonalWeights σ = _
    rw [Matrix.inv_eq_left_inv (RealGeometry.diagonal_inverse σ (fun i => (hσ i).ne')).2]
    simp only [RealGeometry.rotatedGenerator, RealGeometry.diagonalWeights,
      RealGeometry.inverseDiagonalWeights, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hQT : Q.transpose*Q = 1 ∧ Q*Q.transpose = 1 := by
    simpa only [RealGeometry.IsUnitary, Matrix.conjTranspose_eq_transpose_of_trivial] using hQ
  let e : RealVector d := PiLp.single 2 (⟨0, by omega⟩ : Fin d) (1 : ℝ)
  have he0 : e ≠ 0 := by simp [e]
  refine ⟨Q, σ, w, hQT.1, hQT.2, hmono, hσ, hw, hwb, ?_, ?_⟩
  · intro A hA
    rw [he]
    exact inducedNorm_le w _ (fun x => (hwb x).1) a (hwg A hA) e he0
  · intro A hA i j
    rw [he]
    exact hentry A hA i j

#print axioms complex_rounded_extremal_norm
#print axioms real_rounded_extremal_norm
end NLA.MF05.Paper
