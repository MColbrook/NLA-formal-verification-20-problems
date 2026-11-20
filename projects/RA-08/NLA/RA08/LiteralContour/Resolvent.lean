module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace NLA.RA08.Paper.LiteralContour

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

theorem inverse_perturbation_first (a E : A) (t : ℝ)
    (ha : IsUnit a) (hb : IsUnit (a-t • E)) :
    Ring.inverse (a-t • E) = Ring.inverse a + t •
      (Ring.inverse a * E * Ring.inverse (a-t • E)) := by
  have hA := Ring.inverse_mul_cancel a ha
  have hB := Ring.mul_inverse_cancel (a-t • E) hb
  have ht : a * Ring.inverse (a-t • E) =
      1+t • (E * Ring.inverse (a-t • E)) := by
    rw [sub_mul,smul_mul_assoc] at hB
    exact sub_eq_iff_eq_add.mp hB
  calc
    Ring.inverse (a-t • E) = Ring.inverse a * (a * Ring.inverse (a-t • E)) := by
      rw [← mul_assoc,hA,one_mul]
    _ = Ring.inverse a+t • (Ring.inverse a*E*Ring.inverse (a-t • E)) := by
      rw [ht,mul_add,mul_one,mul_smul_comm,mul_assoc]

theorem actual_resolvent_expansion (a E : A) (t : ℝ)
    (ha : IsUnit a) (hb : IsUnit (a-t • E)) :
    Ring.inverse (a-t • E) = Ring.inverse a + t •
      (Ring.inverse a*E*Ring.inverse a) + t^2 •
        (Ring.inverse a*E*Ring.inverse a*E*Ring.inverse (a-t • E)) := by
  have h := inverse_perturbation_first a E t ha hb
  calc
    Ring.inverse (a-t • E) = Ring.inverse a+t •
        (Ring.inverse a*E*Ring.inverse (a-t • E)) := h
    _ = Ring.inverse a+t • (Ring.inverse a*E*(Ring.inverse a+t •
        (Ring.inverse a*E*Ring.inverse (a-t • E)))) :=
      congrArg (fun X => Ring.inverse a+t • (Ring.inverse a*E*X)) h
    _ = _ := by
      simp only [mul_add,mul_smul_comm,smul_add,smul_smul,pow_two,mul_assoc]
      abel

end Algebra

section Normed
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem inverse_perturbation_control (a E : A) (r t : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (htr : t < r/2) (ha : IsUnit a)
    (hR : ‖Ring.inverse a‖ ≤ r⁻¹) (hE : ‖E‖ ≤ 1) :
    IsUnit (a-t • E) ∧ ‖Ring.inverse (a-t • E)‖ ≤ 2*r⁻¹ := by
  have hsmall : ‖Ring.inverse a*(t • E)‖ < 1 := by
    calc
      ‖Ring.inverse a*(t • E)‖ ≤ ‖Ring.inverse a‖*(t*‖E‖) := by
        simpa only [norm_smul,Real.norm_of_nonneg ht] using norm_mul_le (Ring.inverse a) (t • E)
      _ ≤ r⁻¹*(t*1) := by gcongr
      _ < 1 := by
        rw [mul_one]
        have h : t < r := by linarith
        exact (inv_mul_lt_iff₀ hr).2 (by simpa using h)
  have hb : IsUnit (a-t • E) := by
    have h := ha.mul (isUnit_one_sub_of_norm_lt_one hsmall)
    have heq : a*(1-Ring.inverse a*(t • E)) = a-t • E := by
      rw [mul_sub,mul_one,← mul_assoc,Ring.mul_inverse_cancel a ha,one_mul]
    rwa [heq] at h
  refine ⟨hb,?_⟩
  have hnorm : ‖Ring.inverse (a-t • E)‖ ≤ r⁻¹ +
      (t*r⁻¹)*‖Ring.inverse (a-t • E)‖ := by
    calc
      ‖Ring.inverse (a-t • E)‖ = ‖Ring.inverse a+t •
          (Ring.inverse a*E*Ring.inverse (a-t • E))‖ :=
        congrArg norm (inverse_perturbation_first a E t ha hb)
      _ ≤ ‖Ring.inverse a‖ + t *
          (‖Ring.inverse a‖*‖E‖*‖Ring.inverse (a-t • E)‖) := by
        apply (norm_add_le _ _).trans
        rw [norm_smul,Real.norm_of_nonneg ht]
        gcongr
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ r⁻¹ + t*(r⁻¹*1*‖Ring.inverse (a-t • E)‖) := by gcongr
      _ = _ := by ring
  have hhalf : t*r⁻¹ ≤ 1/2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hr).2 (by linarith)
  have hprod := mul_le_mul_of_nonneg_right hhalf (norm_nonneg (Ring.inverse (a-t • E)))
  linarith

end Normed

#print axioms actual_resolvent_expansion
#print axioms inverse_perturbation_control

end NLA.RA08.Paper.LiteralContour
