module

public import NLA.IE21.GaussianClosedForm

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace NLA.IE21.Paper
open NLA.IE21

theorem paper_gaussian_truncated_formula (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (-a)..a, x ^ 2 * gaussianPDFReal 0 1 x) =
      (gaussianReal 0 1).real {x | |x| ≤ a} - 2 * a * gaussianPDFReal 0 1 a := by
  exact gaussian_truncated_density_closed_form a ha

theorem paper_gaussian_closed_form (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    gaussianTrim θ = θ - 2 * gaussianCutoff θ *
      ((1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(gaussianCutoff θ ^ 2) / 2)) := by
  simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div] using
    gaussianTrim_closed_form θ hθ

theorem paper_gaussian_truncated_moment (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1) =
      θ - 2 * gaussianCutoff θ * gaussianPDFReal 0 1 (gaussianCutoff θ) := by
  rw [← gaussianTrim_eq_truncated]
  exact gaussianTrim_closed_form θ hθ

#print axioms paper_gaussian_truncated_formula
#print axioms paper_gaussian_closed_form
#print axioms paper_gaussian_truncated_moment

end NLA.IE21.Paper
