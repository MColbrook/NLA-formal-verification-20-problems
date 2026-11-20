module

public import NLA.IE22.LipschitzPoincare.SmoothApproximation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE22.LipschitzPoincare
open NLA.IE21

theorem truncate_gradient_norm_le {d : ℕ} (f : Space d → ℝ) (n : ℕ) (x : Space d)
    (hx : DifferentiableAt ℝ f x) :
    ‖gradient (atanTruncate n ∘ f) x‖ ≤ ‖gradient f x‖ := by
  have hc := (atanTruncate_hasDerivAt n (f x)).comp_hasFDerivAt x hx.hasFDerivAt
  simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [hc.fderiv, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (atanTruncate_coefficient n (f x)).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (atanTruncate_coefficient n (f x)).2

theorem gaussian_poincare {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) :
    Var[f; stdGaussian (Space d)] ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (Space d) := by
  let μ : Measure (Space d) := stdGaussian (Space d)
  let F : ℕ → Space d → ℝ := fun n => atanTruncate n ∘ f
  have hF (n : ℕ) : LipschitzWith C (F n) := by
    simpa [F] using (atanTruncate_lipschitz n).comp hf
  have hLp : MemLp f 2 μ := lipschitz_space_memLp hf
  have hFi (n : ℕ) : MemLp (F n) 2 μ := lipschitz_space_memLp (hF n)
  have hlim (x : Space d) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    atanTruncate_tendsto (f x)
  have hdom (n : ℕ) (x : Space d) : |F n x| ≤ |f x| := atanTruncate_abs_le n (f x)
  have hmean : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hFi n).aestronglyMeasurable) (hLp.integrable (by norm_num)).abs
    · exact fun n => Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hdom n x
    · exact Eventually.of_forall hlim
  have hsquare : Tendsto (fun n => ∫ x, (F n x)^2 ∂μ) atTop (𝓝 (∫ x, (f x)^2 ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (f x)^2)
      (fun n => ((hF n).continuous.measurable.pow_const 2).aestronglyMeasurable)
      hLp.integrable_sq
    · intro n
      exact Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hdom n x) 2
    · exact Eventually.of_forall fun x => (hlim x).pow 2
  have hvar : Tendsto (fun n => Var[F n; μ]) atTop (𝓝 (Var[f; μ])) := by
    simp only [variance_eq_sub (hFi _), variance_eq_sub hLp, Pi.pow_apply]
    exact hsquare.sub (hmean.pow 2)
  apply le_of_tendsto hvar
  exact Eventually.of_forall fun n => by
    have hb : ∃ B : ℝ, ∀ x, |F n x| ≤ B :=
      ⟨((n : ℝ)+1)*(Real.pi/2), fun x => atanTruncate_bounded n (f x)⟩
    apply (bounded_gaussian_poincare (hF n) hb).trans
    apply integral_mono_ae (gradient_square_integrable (hF n)) (gradient_square_integrable hf)
    filter_upwards [gaussian_ae_gradient hf] with x hx
    exact pow_le_pow_left₀ (norm_nonneg _) (truncate_gradient_norm_le f n x hx.differentiableAt) 2

/-- The all-Lipschitz version of the paper's Gaussian Poincaré assertion.
All moment, integrability and almost-everywhere derivative facts are conclusions. -/
theorem gaussian_poincare_complete {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) :
    MemLp f 2 (stdGaussian (Space d)) ∧
    (∀ᵐ x ∂stdGaussian (Space d), HasGradientAt f (gradient f x) x) ∧
    Integrable (fun x => ‖gradient f x‖ ^ 2) (stdGaussian (Space d)) ∧
    Var[f; stdGaussian (Space d)] ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (Space d) :=
  ⟨lipschitz_space_memLp hf, gaussian_ae_gradient hf, gradient_square_integrable hf,
    gaussian_poincare hf⟩

#print axioms gaussian_poincare_complete
end NLA.IE22.LipschitzPoincare
