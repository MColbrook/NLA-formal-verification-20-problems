module

public import NLA.MD06.QuantitativeCorrection.GradientDefinitions
public import NLA.MD06.GraphCriticalityHessian.GradientPairing

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open scoped BigOperators
open Reference.MD06Actual

theorem actual_euclidean_gradient_norm_squared {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Configuration n) :
    ‖GradientVector G phi‖^2 = ∑ i, (Gradient G (PhaseLift (fun a => phi a)) i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem actual_euclidean_gradient_sum_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Configuration n) : (∑ i, GradientVector G phi i) = 0 :=
  gradient_sum_zero G _

theorem actual_directional_force_gradient_norm_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (phi z : Configuration n) :
    |LineForce G (fun i => phi i) (fun i => z i) 0| ≤ ‖z‖*‖GradientVector G phi‖ := by
  rw [line_force_zero_gradient_pairing]
  have hi : inner ℝ z (GradientVector G phi) =
      ∑ i, z i*Gradient G (PhaseLift (fun a => phi a)) i := by
    simp [PiLp.inner_apply,GradientVector,mul_comm]
  have hp : PhaseLift (fun a => phi a) = (fun a => (phi a : Real.Angle)) := rfl
  rw [hp] at hi
  simpa only [hi] using abs_real_inner_le_norm z (GradientVector G phi)

#print axioms actual_euclidean_gradient_norm_squared
#print axioms actual_euclidean_gradient_sum_zero
#print axioms actual_directional_force_gradient_norm_bound
end Reference.MD06Correction
