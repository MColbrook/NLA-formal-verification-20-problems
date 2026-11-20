module

public import NLA.MD06.GraphCriticalityHessian.Definitions
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open Set

theorem nonnegative_second_derivative_minimum (f g h : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : ∀ t, HasDerivAt g (h t) t)
    (h0 : g 0 = 0) (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ h t) : f 0 ≤ f 1 := by
  have hcg : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hcf : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hmg : MonotoneOn g (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcg.continuousOn
      (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hg t).deriv]; exact hpos t (interior_subset ht))
  have hmf : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcf.continuousOn
      (fun t _ => (hf t).differentiableAt.differentiableWithinAt) (fun t ht => by
        rw [(hf t).deriv]
        have hti : t ∈ Icc (0 : ℝ) 1 := interior_subset ht
        have hm : g 0 ≤ g t := hmg (by simp) hti hti.1
        simpa only [h0] using hm)
  exact hmf (by simp) (by simp) (by norm_num)

#print axioms nonnegative_second_derivative_minimum
end Reference.MD06Actual
