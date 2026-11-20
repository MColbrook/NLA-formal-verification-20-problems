module

public import NLA.MD06.QuantitativeCorrection.BallHessian
public import NLA.MD06.GraphCriticalityHessian.LineDerivatives
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open Set
open Reference.MD06Actual Matrix

theorem actual_derivative_lower_endpoint_growth (f g : ℝ → ℝ) (a : ℝ)
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t ∈ Icc (0 : ℝ) 1, a ≤ g t) :
    f 0+a ≤ f 1 := by
  let F : ℝ → ℝ := fun t => f t-a*t
  have hd : ∀ t, HasDerivAt F (g t-a) t := by
    intro t
    convert! (hf t).sub (hasDerivAt_const_mul a) using 1
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hm : MonotoneOn F (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hc.continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) (fun t ht => by
        rw [(hd t).deriv]
        exact sub_nonneg.mpr (hg t (interior_subset ht)))
  have he : F 0 ≤ F 1 := hm (by simp) (by simp) (by norm_num)
  dsimp [F] at he
  linarith

theorem actual_correction_ball_radial_force_growth {n : ℕ} (G : SimpleGraph (Fin n))
    (phi z : Configuration n) (c : ℝ)
    (hball : ‖z‖ ≤ c/(2*Real.sqrt 2))
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j)) :
    LineForce G (fun i => phi i) (fun i => z i) 0 +
      (c/2)*LaplacianQuadratic G (fun i => z i) ≤
      LineForce G (fun i => phi i) (fun i => z i) 1 := by
  apply actual_derivative_lower_endpoint_growth _ _ _ (line_force_hasDerivAt G _ _)
  intro t ht
  have hb : ‖t • z‖ ≤ c/(2*Real.sqrt 2) := by
    calc
      ‖t • z‖ = t*‖z‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      _ ≤ 1*‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖z‖ := one_mul _
      _ ≤ c/(2*Real.sqrt 2) := hball
  have hh := actual_correction_ball_hessian_laplacian_lower G phi (t • z) z c hb hcos
  rw [actual_laplacian_quadratic_identity] at hh
  rw [line_curvature_actual_hessian]
  have he : PhaseLift (fun i => phi i+(t • z) i) =
      (fun i => ((phi i+t*z i : ℝ) : Real.Angle)) := by funext i; rfl
  rw [he] at hh
  exact hh

#print axioms actual_derivative_lower_endpoint_growth
#print axioms actual_correction_ball_radial_force_growth
end Reference.MD06Correction
