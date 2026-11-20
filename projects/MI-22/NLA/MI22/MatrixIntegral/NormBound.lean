module

public import NLA.MI22.MatrixIntegral.IntegralIdentities
public import NLA.MI22.LiteralDerivative.Proof

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NLA.RA09.LiteralIntegral NLA.MI22.LiteralDerivative

namespace NLA.MI22.MatrixIntegral

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem resolvent_norm_bound (t m : ℝ) (ht : 0 < t) (hm : 0 < m)
    (a : A) (ha : 0 ≤ a) (hma : algebraMap ℝ A m ≤ a) :
    ‖resolvent t a‖ ≤ (t+m)⁻¹ := by
  rw [resolvent_eq_cfc t ht a ha]
  apply norm_cfc_le (by positivity)
  intro z hz
  have hmz := (algebraMap_le_iff_le_spectrum ha.isSelfAdjoint).mp hma z hz
  have htz : 0 < t+z := by linarith
  rw [Real.norm_of_nonneg (inv_nonneg.mpr htz.le)]
  exact inv_anti₀ (by positivity) (by linarith)

theorem difference_kernel_norm_bound (p t m : ℝ) (ht : 0 < t) (hm : 0 < m)
    (P Q : A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hmP : algebraMap ℝ A m ≤ P) (hmQ : algebraMap ℝ A m ≤ Q) :
    ‖differenceKernel p t P Q‖ ≤ derivativeIntegrand p m t * ‖P-Q‖ := by
  have hnP := resolvent_norm_bound t m ht hm P hP hmP
  have hnQ := resolvent_norm_bound t m ht hm Q hQ hmQ
  unfold differenceKernel derivativeIntegrand
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le p)]
  calc
    t^p * ‖resolvent t Q * (P-Q) * resolvent t P‖ ≤
        t^p * (‖resolvent t Q‖ * ‖P-Q‖ * ‖resolvent t P‖) := by
      gcongr
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ t^p * ((t+m)⁻¹ * ‖P-Q‖ * (t+m)⁻¹) := by gcongr
    _ = t^p / (t+m)^2 * ‖P-Q‖ := by field_simp

theorem power_difference_bound_by_integral (p m : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hm : 0 < m) (P Q : A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hmP : algebraMap ℝ A m ≤ P) (hmQ : algebraMap ℝ A m ≤ Q) :
    ‖CFC.rpow P p - CFC.rpow Q p‖ ≤ p*m^(p-1)*‖P-Q‖ := by
  rw [difference_integral_representation p hp hp1 P Q hP hQ, norm_smul,
    Real.norm_of_nonneg (normalization_pos p hp hp1).le]
  have hi := (actual_derivative_integrable p m hp hp1 hm).mul_const ‖P-Q‖
  have hn : ‖∫ t in Ioi 0, differenceKernel p t P Q‖ ≤
      ∫ t in Ioi 0, derivativeIntegrand p m t * ‖P-Q‖ := by
    apply norm_integral_le_of_norm_le hi
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
      difference_kernel_norm_bound p t m ht hm P Q hP hQ hmP hmQ
  have hv : normalization p * (∫ t in Ioi 0, derivativeIntegrand p m t) =
      p*m^(p-1) := actual_literal_derivative_formula p m hp hp1 hm
  calc
    normalization p * ‖∫ t in Ioi 0, differenceKernel p t P Q‖ ≤
      normalization p * ∫ t in Ioi 0, derivativeIntegrand p m t * ‖P-Q‖ :=
        mul_le_mul_of_nonneg_left hn (normalization_pos p hp hp1).le
    _ = p*m^(p-1)*‖P-Q‖ := by rw [integral_mul_const, ← mul_assoc, hv]

#print axioms difference_kernel_norm_bound
#print axioms power_difference_bound_by_integral

end CStar
end NLA.MI22.MatrixIntegral
