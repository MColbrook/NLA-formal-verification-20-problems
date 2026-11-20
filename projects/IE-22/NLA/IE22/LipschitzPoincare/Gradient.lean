module

public import NLA.IE22.LipschitzPoincare.Scalar
public import Mathlib.Analysis.Calculus.Gradient.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE22.LipschitzPoincare
open NLA.IE21

theorem lipschitz_space_memLp {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) : MemLp f 2 (stdGaussian (Space d)) := by
  have hl : LipschitzWith C (fun x => f x - f 0) :=
    LipschitzWith.of_dist_le_mul fun x y => by simpa using hf.dist_le_mul x y
  have hh := hl.comp_memLp (by simp)
    (IsGaussian.memLp_two_id (μ := stdGaussian (Space d)))
  have ha := hh.add (memLp_const (f 0))
  convert ha using 1
  ext x
  simp

theorem gradient_measurable {d : ℕ} (f : Space d → ℝ) : Measurable (gradient f) := by
  exact (InnerProductSpace.toDual ℝ (Space d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ f)

theorem gradient_norm_le {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) (x : Space d) : ‖gradient f x‖ ≤ C := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    (norm_fderiv_le_of_lipschitz (𝕜 := ℝ) (x₀ := x) hf)

theorem gaussian_ae_gradient {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) : ∀ᵐ x ∂stdGaussian (Space d), HasGradientAt f (gradient f x) x := by
  have hac : stdGaussian (Space d) ≪ (volume : Measure (Space d)) := by
    rw [stdGaussian_radial_density]
    exact withDensity_absolutelyContinuous _ _
  exact ((hf.ae_differentiableAt (μ := volume)).filter_mono hac.ae_le).mono
    fun _ h => h.hasGradientAt

theorem gradient_square_integrable {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) :
    Integrable (fun x => ‖gradient f x‖ ^ 2) (stdGaussian (Space d)) := by
  have hLp : MemLp (fun x => ‖gradient f x‖) 2 (stdGaussian (Space d)) :=
    MemLp.of_bound (gradient_measurable f).norm.aestronglyMeasurable C
      (Eventually.of_forall fun x => by simpa using gradient_norm_le hf x)
  exact hLp.integrable_sq

theorem gradient_coordinate {d : ℕ} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    gradient f x i = (fderiv ℝ f x) (EuclideanSpace.basisFun (Fin d) ℝ i) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]

theorem gradient_norm_sq {d : ℕ} (f : Space d → ℝ) (x : Space d) :
    ‖gradient f x‖ ^ 2 = ∑ i, ((fderiv ℝ f x) (EuclideanSpace.basisFun (Fin d) ℝ i)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [gradient_coordinate]

#print axioms gaussian_ae_gradient
end NLA.IE22.LipschitzPoincare
