module

public import NLA.RA08.PaperNuclearTriangularDefinitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclear_sine_recurrence (x θ : ℝ) :
    2*Real.sin x-Real.sin (x-θ)-Real.sin (x+θ) =
      4*Real.sin (θ/2)^2*Real.sin x := by
  have hc : Real.cos θ=1-2*Real.sin (θ/2)^2 := by
    have h := Real.cos_two_mul (θ/2)
    have hs := Real.sin_sq_add_cos_sq (θ/2)
    rw [show 2*(θ/2)=θ by ring] at h
    nlinarith
  rw [Real.sin_sub,Real.sin_add,hc]
  ring

theorem nuclearSineAngle_pos {m : ℕ} (j : Fin m) :
    0 < nuclearSineAngle j := by
  unfold nuclearSineAngle
  apply div_pos
  · exact mul_pos (by positivity) Real.pi_pos
  · positivity

theorem nuclearSineAngle_lt_pi {m : ℕ} (j : Fin m) :
    nuclearSineAngle j < Real.pi := by
  unfold nuclearSineAngle
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*m+1)).mpr
  have hj : ((2*j.val+1 : ℕ) : ℝ) < 2*m+1 := by exact_mod_cast (by omega : 2*j.val+1 < 2*m+1)
  nlinarith [Real.pi_pos]

theorem nuclearSineAngle_boundary {m : ℕ} (j : Fin m) :
    Real.sin (((m+1 : ℕ) : ℝ)*nuclearSineAngle j) =
      Real.sin ((m : ℝ)*nuclearSineAngle j) := by
  have hd : (2*(m : ℝ)+1) ≠ 0 := by positivity
  have ha : ((m+1 : ℕ) : ℝ)*nuclearSineAngle j =
      ((2*j.val+1 : ℕ) : ℝ)*Real.pi-(m : ℝ)*nuclearSineAngle j := by
    unfold nuclearSineAngle
    push_cast
    field_simp
    ring
  rw [ha,Real.sin_nat_mul_pi_sub]
  simp [pow_add,pow_mul]

theorem nuclearSineVector_ne_zero {m : ℕ} (j : Fin m) :
    nuclearSineVector j ≠ 0 := by
  intro h
  have hj := j.isLt
  let i : Fin m := ⟨0,by omega⟩
  have hs : 0 < nuclearSineVector j i := by
    simpa [nuclearSineVector,i] using
      Real.sin_pos_of_pos_of_lt_pi (nuclearSineAngle_pos j) (nuclearSineAngle_lt_pi j)
  have hz := congrFun h i
  simp only [Pi.zero_apply] at hz
  linarith

theorem nuclearDifferenceEigenvalue_eq {m : ℕ} (j : Fin m) :
    nuclearDifferenceEigenvalue j=2-2*Real.cos (nuclearSineAngle j) := by
  have h := Real.cos_two_mul (nuclearSineAngle j/2)
  have hs := Real.sin_sq_add_cos_sq (nuclearSineAngle j/2)
  rw [show 2*(nuclearSineAngle j/2)=nuclearSineAngle j by ring] at h
  unfold nuclearDifferenceEigenvalue
  nlinarith

theorem nuclearDifferenceEigenvalue_injective (m : ℕ) :
    Function.Injective (nuclearDifferenceEigenvalue (m := m)) := by
  intro i j hij
  rw [nuclearDifferenceEigenvalue_eq,nuclearDifferenceEigenvalue_eq] at hij
  have hc : Real.cos (nuclearSineAngle i)=Real.cos (nuclearSineAngle j) := by linarith
  have ha := Real.injOn_cos ⟨(nuclearSineAngle_pos i).le,(nuclearSineAngle_lt_pi i).le⟩
    ⟨(nuclearSineAngle_pos j).le,(nuclearSineAngle_lt_pi j).le⟩ hc
  unfold nuclearSineAngle at ha
  have hd : (2*(m : ℝ)+1) ≠ 0 := by positivity
  have hp := Real.pi_ne_zero
  have hi : (i.val : ℝ)=(j.val : ℝ) := by
    apply_fun (fun x : ℝ => x*(2*m+1)) at ha
    field_simp at ha
    push_cast at ha
    nlinarith
  apply Fin.ext
  exact_mod_cast hi

#print axioms nuclearSineAngle_boundary
end NLA.RA08.Paper
