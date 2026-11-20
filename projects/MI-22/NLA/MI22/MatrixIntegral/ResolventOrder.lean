module

public import NLA.MI22.MatrixIntegral.KernelAlgebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace NLA.MI22.MatrixIntegral

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem multiplicative_resolvent_identity (t : ℝ) (ht : 0 < t) (a : A) (ha : 0 ≤ a) :
    a * resolvent t a = 1 - t • resolvent t a := by
  have h := Ring.mul_inverse_cancel (algebraMap ℝ A t + a) (shifted_isUnit t ht a ha)
  rw [add_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
  apply eq_sub_iff_add_eq.mpr
  simpa only [resolvent, Algebra.algebraMap_eq_smul_one, add_comm] using h

theorem multiplicative_resolvent_monotone (t : ℝ) (ht : 0 < t) (P Q : A)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hPQ : P ≤ Q) :
    P * resolvent t P ≤ Q * resolvent t Q := by
  have hmap : 0 ≤ algebraMap ℝ A t := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_nonneg ht.le (show (0 : A) ≤ 1 from zero_le_one)
  have hposP : IsStrictlyPositive (algebraMap ℝ A t + P) :=
    ⟨add_nonneg hmap hP, shifted_isUnit t ht P hP⟩
  have hposQ : IsStrictlyPositive (algebraMap ℝ A t + Q) :=
    ⟨add_nonneg hmap hQ, shifted_isUnit t ht Q hQ⟩
  have hi : resolvent t Q ≤ resolvent t P :=
    CStarAlgebra.antitoneOn_ringInverse hposP hposQ (add_le_add le_rfl hPQ)
  rw [multiplicative_resolvent_identity t ht P hP,
    multiplicative_resolvent_identity t ht Q hQ]
  exact sub_le_sub_left (smul_le_smul_of_nonneg_left hi ht.le) 1

#print axioms multiplicative_resolvent_monotone

end CStar
end NLA.MI22.MatrixIntegral
