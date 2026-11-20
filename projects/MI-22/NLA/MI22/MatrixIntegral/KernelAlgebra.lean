module

public import NLA.MI22.MatrixIntegral.Definitions
public import NLA.MI22.MatrixIntegral.CFCIntegral
public import Mathlib.Algebra.Ring.Invertible

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NLA.RA09.LiteralIntegral

namespace NLA.MI22.MatrixIntegral

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem shifted_isUnit (t : ℝ) (ht : 0 < t) (a : A) (ha : 0 ≤ a) :
    IsUnit (algebraMap ℝ A t + a) := by
  have hspec : ∀ z ∈ spectrum ℝ a, t+z ≠ 0 := by
    intro z hz
    have := spectrum_nonnegative a ha hz
    linarith
  have h := (isUnit_cfc_iff (fun z : ℝ => t+z) a (by fun_prop) ha.isSelfAdjoint).mpr hspec
  rwa [cfc_const_add t (fun z : ℝ => z) a continuous_id.continuousOn ha.isSelfAdjoint,
    cfc_id' ℝ a ha.isSelfAdjoint] at h

theorem resolvent_eq_cfc (t : ℝ) (ht : 0 < t) (a : A) (ha : 0 ≤ a) :
    resolvent t a = cfc (fun z : ℝ => (t+z)⁻¹) a := by
  have hspec : ∀ z ∈ spectrum ℝ a, t+z ≠ 0 := by
    intro z hz
    have := spectrum_nonnegative a ha hz
    linarith
  have h := cfc_inv (fun z : ℝ => t+z) a hspec (by fun_prop) ha.isSelfAdjoint
  rw [cfc_const_add t (fun z : ℝ => z) a continuous_id.continuousOn ha.isSelfAdjoint,
    cfc_id' ℝ a ha.isSelfAdjoint] at h
  unfold resolvent
  exact h.symm

theorem cfc_kernel_eq_sub (p t : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (a : A) (ha : 0 ≤ a) :
    cfc (Real.rpowIntegrand₀₁ p t) a =
      algebraMap ℝ A (t^(p-1)) - t^p • resolvent t a := by
  have hs : ∀ z ∈ spectrum ℝ a, t+z ≠ 0 := by
    intro z hz
    have := spectrum_nonnegative a ha hz
    linarith
  have hg : ContinuousOn (fun z : ℝ => (t+z)⁻¹) (spectrum ℝ a) :=
    (continuous_const.add continuous_id).continuousOn.inv₀ hs
  rw [Real.rpowIntegrand₀₁_eq_sub (by linarith) ht,
    cfc_sub _ _ a (by fun_prop) (hg.const_mul _), cfc_const (t^(p-1)) a ha.isSelfAdjoint,
    cfc_const_mul _ _ a hg, ← resolvent_eq_cfc t ht a ha]

theorem cfc_kernel_eq_powerKernel (p t : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (a : A) (ha : 0 ≤ a) :
    cfc (Real.rpowIntegrand₀₁ p t) a = powerKernel p t a := by
  have hs : ∀ z ∈ spectrum ℝ a, t+z ≠ 0 := by
    intro z hz
    have := spectrum_nonnegative a ha hz
    linarith
  have hg : ContinuousOn (fun z : ℝ => (t+z)⁻¹) (spectrum ℝ a) :=
    (continuous_const.add continuous_id).continuousOn.inv₀ hs
  have he : cfc (Real.rpowIntegrand₀₁ p t) a =
      cfc (fun z : ℝ => t^(p-1) * (z * (t+z)⁻¹)) a := by
    apply cfc_congr
    intro z hz
    rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp,hp1⟩ ht.le (spectrum_nonnegative a ha hz)]
    simp only [div_eq_mul_inv, mul_assoc]
  rw [he, cfc_const_mul (t^(p-1)) (fun z : ℝ => z*(t+z)⁻¹) a
      (by exact continuous_id.continuousOn.mul hg),
    cfc_mul (fun z : ℝ => z) (fun z : ℝ => (t+z)⁻¹) a continuous_id.continuousOn hg,
    cfc_id' ℝ a ha.isSelfAdjoint,
    ← resolvent_eq_cfc t ht a ha]
  rfl

theorem resolvent_difference (t : ℝ) (ht : 0 < t) (P Q : A)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    resolvent t Q - resolvent t P = resolvent t Q * (P-Q) * resolvent t P := by
  have h := Ring.inverse_sub_inverse
    (show IsUnit (algebraMap ℝ A t + Q) ↔ IsUnit (algebraMap ℝ A t + P)
      from ⟨fun _ => shifted_isUnit t ht P hP, fun _ => shifted_isUnit t ht Q hQ⟩)
  have he : (algebraMap ℝ A t + P) - (algebraMap ℝ A t + Q) = P-Q := by abel
  simpa only [he, resolvent] using h

theorem kernel_difference (p t : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (ht : 0 < t) (P Q : A) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    powerKernel p t P - powerKernel p t Q = differenceKernel p t P Q := by
  rw [← cfc_kernel_eq_powerKernel p t hp hp1 ht P hP,
    ← cfc_kernel_eq_powerKernel p t hp hp1 ht Q hQ,
    cfc_kernel_eq_sub p t hp hp1 ht P hP, cfc_kernel_eq_sub p t hp hp1 ht Q hQ]
  have he : algebraMap ℝ A (t^(p-1)) - t^p • resolvent t P -
      (algebraMap ℝ A (t^(p-1)) - t^p • resolvent t Q) =
      t^p • (resolvent t Q - resolvent t P) := by rw [smul_sub]; abel
  rw [he, resolvent_difference t ht P Q hP hQ]
  rfl

#print axioms kernel_difference

end CStar
end NLA.MI22.MatrixIntegral
