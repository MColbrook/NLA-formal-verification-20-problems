module

public import NLA.RA09.PaperGaussianTrace

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace NLA.RA09.Paper

/-- Every real symmetric residual, sampled against the actual standard Gaussian measure. -/
theorem paper_gaussian_trace_variance {n : ℕ} (R : RealMatrix n) (hR : R.IsHermitian) :
    Var[fun g : EuclideanSpace ℝ (Fin n) =>
      dotProduct (fun i => g i) (R *ᵥ (fun i => g i));
      stdGaussian (EuclideanSpace ℝ (Fin n))] = 2 * frobeniusNorm R ^ 2 := by
  exact gaussian_trace_variance R hR

#print axioms paper_gaussian_trace_variance
end NLA.RA09.Paper
