module

public import NLA.MI22.MatrixIntegral.KernelAlgebra

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NLA.RA09.LiteralIntegral

namespace NLA.MI22.MatrixIntegral

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem power_kernel_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : A) (ha : 0 ≤ a) : IntegrableOn (fun t => powerKernel p t a) (Ioi 0) := by
  refine (cfc_kernel_integral p hp hp1 a ha).1.congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact cfc_kernel_eq_powerKernel p t hp hp1 ht a ha

theorem power_integral_representation (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : A) (ha : 0 ≤ a) :
    CFC.rpow a p = normalization p • ∫ t in Ioi 0, powerKernel p t a := by
  rw [(cfc_kernel_integral p hp hp1 a ha).2]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact cfc_kernel_eq_powerKernel p t hp hp1 ht a ha

theorem difference_kernel_integrable (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (P Q : A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    IntegrableOn (fun t => differenceKernel p t P Q) (Ioi 0) := by
  refine ((power_kernel_integrable p hp hp1 P hP).sub
    (power_kernel_integrable p hp hp1 Q hQ)).congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact kernel_difference p t hp hp1 ht P Q hP hQ

theorem difference_integral_representation (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (P Q : A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    CFC.rpow P p - CFC.rpow Q p =
      normalization p • ∫ t in Ioi 0, differenceKernel p t P Q := by
  rw [power_integral_representation p hp hp1 P hP,
    power_integral_representation p hp hp1 Q hQ, ← smul_sub,
    ← integral_sub (power_kernel_integrable p hp hp1 P hP)
      (power_kernel_integrable p hp hp1 Q hQ)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact kernel_difference p t hp hp1 ht P Q hP hQ

#print axioms power_integral_representation
#print axioms difference_integral_representation
#print axioms difference_kernel_integrable

end CStar
end NLA.MI22.MatrixIntegral
