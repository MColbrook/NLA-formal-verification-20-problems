module

public import NLA.MD06.QuantitativeCorrection.CompactBall
public import NLA.MD06.GraphCriticalityHessian.LineDerivatives
public import Mathlib.Analysis.Calculus.Darboux

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open Set
open scoped BigOperators
open Reference.MD06Actual

theorem actual_right_endpoint_minimum_derivative_nonpositive (f : ℝ → ℝ) (a : ℝ)
    (hf : HasDerivAt f a 1) (hmin : ∀ t ∈ Icc (0 : ℝ) 1, f 1 ≤ f t) : a ≤ 0 := by
  have hm : IsMinOn f (Icc (0 : ℝ) 1) 1 := hmin
  have ht : (0 : ℝ)-1 ∈ posTangentConeAt (Icc (0 : ℝ) 1) 1 :=
    sub_mem_posTangentConeAt_of_segment_subset (by
      rw [segment_symm,segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)])
  have hn := hm.localize.hasFDerivWithinAt_nonneg hf.hasFDerivAt.hasFDerivWithinAt ht
  simpa [ContinuousLinearMap.smulRight_apply] using hn

theorem actual_slice_ball_minimizer_radial_force_nonpositive {n : ℕ} (G : SimpleGraph (Fin n))
    (phi h : Configuration n) (rho : ℝ) (hzero : (∑ i, h i) = 0) (hnorm : ‖h‖ ≤ rho)
    (hmin : ∀ g ∈ CorrectionBall n rho, LiftedEnergy G (phi+h) ≤ LiftedEnergy G (phi+g)) :
    LineForce G (fun i => phi i) (fun i => h i) 1 ≤ 0 := by
  apply actual_right_endpoint_minimum_derivative_nonpositive _ _ (line_energy_hasDerivAt G _ _ 1)
  intro t ht
  have hb : t • h ∈ CorrectionBall n rho := by
    constructor
    · simp only [PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum,hzero,mul_zero]
    · calc
        ‖t • h‖ = t*‖h‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        _ ≤ 1*‖h‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ = ‖h‖ := one_mul _
        _ ≤ rho := hnorm
  have hl : ∀ s : ℝ, LineEnergy G (fun i => phi i) (fun i => h i) s =
      LiftedEnergy G (phi+s • h) := by
    intro s
    rw [line_energy_actual]
    rfl
  calc
    LineEnergy G (fun i => phi i) (fun i => h i) 1 = LiftedEnergy G (phi+h) := by rw [hl,one_smul]
    _ ≤ LiftedEnergy G (phi+t • h) := hmin _ hb
    _ = LineEnergy G (fun i => phi i) (fun i => h i) t := (hl t).symm

#print axioms actual_right_endpoint_minimum_derivative_nonpositive
#print axioms actual_slice_ball_minimizer_radial_force_nonpositive
end Reference.MD06Correction
