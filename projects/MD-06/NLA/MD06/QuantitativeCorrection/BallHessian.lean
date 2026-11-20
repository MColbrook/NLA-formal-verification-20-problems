module

public import NLA.MD06.QuantitativeCorrection.EdgeEstimates
public import NLA.MD06.GraphCriticalityHessian.Laplacian

@[expose] public section
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reference.MD06Correction
open Reference.MD06Actual Matrix

theorem actual_correction_ball_hessian_laplacian_lower {n : ℕ} (G : SimpleGraph (Fin n))
    (phi h z : Configuration n) (c : ℝ)
    (hball : ‖h‖ ≤ c/(2*Real.sqrt 2))
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j)) :
    (c/2) * ((fun i => z i) ⬝ᵥ (G.lapMatrix ℝ) *ᵥ (fun i => z i)) ≤
      HessianQuadratic G (PhaseLift (fun i => phi i+h i)) (fun i => z i) := by
  apply hessian_lower_bound_actual_laplacian
  intro i j hij
  have hb := actual_correction_ball_edge_cosines G phi h c hball hcos i j hij
  simpa only [PhaseLift,← Real.Angle.coe_sub,Real.Angle.cos_coe] using hb

#print axioms actual_correction_ball_hessian_laplacian_lower
end Reference.MD06Correction
