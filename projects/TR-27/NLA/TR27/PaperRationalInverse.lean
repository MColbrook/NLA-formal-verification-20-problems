module

public import NLA.TR27.PaperRecoveryMoment
public import NLA.TR27.PaperHomogeneous
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Coeff

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

@[simp] theorem recoveryIndex_source_value (D : ℕ) (hD : 5 ≤ D) (hD' : 2 ≤ D) (j : Fin 4) :
    (retainedIndex D hD' (recoveryIndex D hD j)).val = j.val+2 := by
  simp [retainedIndex, pivotIndex, recoveryIndex, Fin.succAbove, Fin.lt_def, Nat.add_assoc]

theorem recovery_curve_coordinate (D r : ℕ) (hD : 5 ≤ D) (j : Fin 4) (t : ℂ) :
    coordinateCurve D r (by omega) (some t) (recoveryIndex D hD j) =
      chosenPivot r * t^(j.val+2) - chosenPowerSum r (j.val+2)*t := by
  simp [coordinateCurve, coordinateProjection, curveVector, pivotIndex, recoveryIndex_source_value]

theorem recoveryDenominator_curve (D r : ℕ) (hD : 5 ≤ D) (t : ℂ) :
    MvPolynomial.eval (coordinateCurve D r (by omega) (some t)) (recoveryDenominator D r hD) =
      Polynomial.eval t (recoveryPolynomial r) := by
  simp only [recoveryDenominator, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, recovery_curve_coordinate]
  simp only [recoveryPolynomial, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  norm_num
  dsimp only [recoveryMomentA, recoveryMomentB, recoveryMomentC]
  ring

theorem recoveryNumerator_curve (D r : ℕ) (hD : 5 ≤ D) (t : ℂ) :
    MvPolynomial.eval (coordinateCurve D r (by omega) (some t)) (recoveryNumerator D r hD) =
      t * MvPolynomial.eval (coordinateCurve D r (by omega) (some t)) (recoveryDenominator D r hD) := by
  simp only [recoveryNumerator, recoveryDenominator, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, recovery_curve_coordinate]
  norm_num
  dsimp only [recoveryMomentA, recoveryMomentB, recoveryMomentC]
  ring

theorem recoveryPolynomial_ne_zero {r : ℕ} (hr : 3 ≤ r) : recoveryPolynomial r ≠ 0 := by
  unfold recoveryPolynomial
  apply mul_ne_zero
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr (chosenPivot_ne_zero hr))
      (pow_ne_zero _ Polynomial.X_ne_zero)
  · intro h
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 2) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at hc
    norm_num at hc
    exact recoveryMomentC_ne_zero (by omega) hc

theorem recoveryDenominator_smul (D r : ℕ) (hD : 5 ≤ D) (c : ℂ) (w : Fin D → ℂ) :
    MvPolynomial.eval (c • w) (recoveryDenominator D r hD) =
      c * MvPolynomial.eval w (recoveryDenominator D r hD) := by
  simp only [recoveryDenominator, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
  ring

theorem recoveryNumerator_smul (D r : ℕ) (hD : 5 ≤ D) (c : ℂ) (w : Fin D → ℂ) :
    MvPolynomial.eval (c • w) (recoveryNumerator D r hD) =
      c * MvPolynomial.eval w (recoveryNumerator D r hD) := by
  simp only [recoveryNumerator, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Pi.smul_apply, smul_eq_mul]
  ring

theorem rationalRecovery_smul (D r : ℕ) (hD : 5 ≤ D) (c : ℂ) (hc : c ≠ 0) (w : Fin D → ℂ) :
    rationalRecovery D r hD (c • w) = rationalRecovery D r hD w := by
  rw [rationalRecovery, recoveryNumerator_smul, recoveryDenominator_smul]
  exact mul_div_mul_left _ _ hc

theorem rationalRecovery_curve (D r : ℕ) (hD : 5 ≤ D) (t : ℂ)
    (ht : Polynomial.eval t (recoveryPolynomial r) ≠ 0) :
    rationalRecovery D r hD (coordinateCurve D r (by omega) (some t)) = t := by
  unfold rationalRecovery
  rw [recoveryNumerator_curve, recoveryDenominator_curve]
  exact mul_div_cancel_right₀ t ht

theorem recovery_exceptional_parameters_finite (r : ℕ) (hr : 3 ≤ r) :
    Set.Finite {t : ℂ | Polynomial.eval t (recoveryPolynomial r) = 0} := by
  exact Polynomial.finite_setOfPred_isRoot (recoveryPolynomial_ne_zero hr)

theorem recovery_regular_parameter_exists (r : ℕ) (hr : 3 ≤ r) :
    ∃ t : ℂ, Polynomial.eval t (recoveryPolynomial r) ≠ 0 := by
  by_contra h
  push Not at h
  apply recoveryPolynomial_ne_zero hr
  apply Polynomial.funext
  intro t
  simp only [h, Polynomial.eval_zero]

theorem rationalRecovery_projective_rep (D r : ℕ) (hD : 5 ≤ D) (t : ℂ)
    (p : ℙ ℂ (Fin D → ℂ)) (hp : Represents (coordinateCurve D r (by omega) (some t)) p)
    (hden : MvPolynomial.eval p.rep (recoveryDenominator D r hD) ≠ 0) :
    rationalRecovery D r hD p.rep = t := by
  obtain ⟨c,hc,heq⟩ := hp
  rw [heq, rationalRecovery_smul D r hD c hc]
  apply rationalRecovery_curve
  rw [heq, recoveryDenominator_smul, recoveryDenominator_curve] at hden
  exact (mul_ne_zero_iff.mp hden).2

#print axioms recoveryPolynomial_ne_zero
#print axioms rationalRecovery_projective_rep
#print axioms recovery_exceptional_parameters_finite
end NLA.TR27.Paper
