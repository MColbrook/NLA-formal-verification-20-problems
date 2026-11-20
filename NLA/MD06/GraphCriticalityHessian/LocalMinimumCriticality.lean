module

public import NLA.MD06.GraphCriticalityHessian.GradientPairing
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open scoped BigOperators Topology

theorem actual_angle_local_min_line_force_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Fin n → ℝ) (hmin : IsLocalMin (Energy G) (fun i => (phi i : Real.Angle)))
    (z : Fin n → ℝ) : LineForce G phi z 0 = 0 := by
  let curve : ℝ → Phase n := fun t i => ((phi i+t*z i : ℝ) : Real.Angle)
  have hc : Continuous curve := by
    apply continuous_pi
    intro i
    exact Real.Angle.continuous_coe.comp (by fun_prop)
  have he : curve 0 = fun i => (phi i : Real.Angle) := by
    funext i
    simp only [curve,zero_mul,add_zero]
  have hm0 : IsLocalMin (Energy G) (curve 0) := he.symm ▸ hmin
  have hm : IsLocalMin (Energy G ∘ curve) 0 := hm0.comp_continuous hc.continuousAt
  have hf : LineEnergy G phi z = Energy G ∘ curve := by
    funext t
    rw [line_energy_actual,real_energy_angle_lift]
    rfl
  rw [← hf] at hm
  exact hm.hasDerivAt_eq_zero (line_energy_hasDerivAt G phi z 0)

theorem actual_angle_local_min_gradient_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (hmin : IsLocalMin (Energy G) theta) :
    ∀ i, Gradient G theta i = 0 := by
  let phi : Fin n → ℝ := fun i => (theta i).toReal
  have he : (fun i => (phi i : Real.Angle)) = theta := by
    funext i
    exact Real.Angle.coe_toReal (theta i)
  have hm : IsLocalMin (Energy G) (fun i => (phi i : Real.Angle)) := he.symm ▸ hmin
  have hg := (actual_critical_iff_all_line_forces_zero G phi).mpr
    (actual_angle_local_min_line_force_zero G phi hm)
  rw [he] at hg
  exact hg

#print axioms actual_angle_local_min_line_force_zero
#print axioms actual_angle_local_min_gradient_zero
end Reference.MD06Actual
