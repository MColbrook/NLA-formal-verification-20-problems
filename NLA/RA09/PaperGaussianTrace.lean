module

public import NLA.RA09.PaperGaussianSquare
public import NLA.RA09.Frobenius
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
namespace NLA.RA09.Paper

theorem quadratic_eigenbasis {n : ℕ} (R : RealMatrix n) (hR : R.IsHermitian)
    (x : Fin n → ℝ) :
    ⟪∑ i, x i • hR.eigenvectorBasis i,
      R.toEuclideanLin (∑ i, x i • hR.eigenvectorBasis i)⟫ =
      ∑ i, hR.eigenvalues i * x i ^ 2 := by
  have he (i : Fin n) : R.toEuclideanLin (hR.eigenvectorBasis i) =
      hR.eigenvalues i • hR.eigenvectorBasis i := by
    apply PiLp.ext
    intro j
    exact congrFun (hR.mulVec_eigenvectorBasis i) j
  simp only [map_sum, map_smul, he, smul_smul]
  rw [hR.eigenvectorBasis.orthonormal.inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [starRingEnd_apply, star_trivial]
  ring

theorem frobenius_eigenvalues {n : ℕ} (R : RealMatrix n) (hR : R.IsHermitian) :
    frobeniusSquared R = ∑ i, hR.eigenvalues i ^ 2 := by
  have hspec : R = (hR.eigenvectorUnitary : RealMatrix n) *
      Matrix.diagonal hR.eigenvalues * (hR.eigenvectorUnitary : RealMatrix n).transpose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using hR.spectral_theorem
  conv_lhs => rw [hspec]
  have hs : (hR.eigenvectorUnitary : RealMatrix n).transpose =
      (star hR.eigenvectorUnitary : Matrix.unitaryGroup (Fin n) ℝ) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hs, frobenius_orthogonal_invariance_proved]
  simp [frobeniusSquared, Matrix.diagonal_apply]

theorem gaussian_trace_variance_inner {n : ℕ} (R : RealMatrix n) (hR : R.IsHermitian) :
    Var[fun g : EuclideanSpace ℝ (Fin n) => ⟪g, R.toEuclideanLin g⟫;
      stdGaussian (EuclideanSpace ℝ (Fin n))] = 2 * frobeniusNorm R ^ 2 := by
  have hc : Continuous (fun g : EuclideanSpace ℝ (Fin n) => ⟪g, R.toEuclideanLin g⟫) :=
    continuous_id.inner R.toEuclideanLin.continuous_of_finiteDimensional
  rw [stdGaussian_eq_map_pi_orthonormalBasis hR.eigenvectorBasis,
    variance_map hc.aemeasurable (Measurable.aemeasurable (by fun_prop))]
  have hf : (fun g : EuclideanSpace ℝ (Fin n) => ⟪g, R.toEuclideanLin g⟫) ∘
      (fun x : Fin n → ℝ => ∑ i, x i • hR.eigenvectorBasis i) =
      ∑ i, (fun x : Fin n → ℝ => hR.eigenvalues i * x i ^ 2) := by
    funext x
    simpa using quadratic_eigenbasis R hR x
  rw [hf, variance_sum_pi (fun i => gaussian_square_memLp.const_mul (hR.eigenvalues i))]
  simp_rw [variance_const_mul, gaussian_square_variance]
  rw [← frobeniusSquared_norm, frobenius_eigenvalues R hR, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The literal real quadratic form, including the zero-dimensional case. -/
theorem gaussian_trace_variance {n : ℕ} (R : RealMatrix n) (hR : R.IsHermitian) :
    Var[fun g : EuclideanSpace ℝ (Fin n) =>
      dotProduct (fun i => g i) (R *ᵥ (fun i => g i));
      stdGaussian (EuclideanSpace ℝ (Fin n))] = 2 * frobeniusNorm R ^ 2 := by
  simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toLpLin_apply, dotProduct_comm] using
    gaussian_trace_variance_inner R hR

#print axioms gaussian_trace_variance
end NLA.RA09.Paper
