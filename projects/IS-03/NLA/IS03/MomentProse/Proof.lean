module

public import NLA.IS03.Proof
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.IS03.MomentProse

theorem root_power_moments {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (hcard : Fintype.card ι = 6)
    (hprod : (∏ i, (X - C (μ i))) = derivativePolynomial.map (algebraMap ℝ ℂ)) :
    ∀ i : Fin 7, (∑ j, μ j ^ (i.val+1)) = (traceMoments i : ℂ) := by
  exact power_sums_of_derivative_product μ hcard hprod

theorem matrix_trace_moments (B : RealMatrix 6)
    (hB : B.charpoly = derivativePolynomial) :
    ∀ i : Fin 7, Matrix.trace (B^(i.val+1)) = traceMoments i := by
  exact trace_moment_certificate_proved B hB

theorem first_six_positive : ∀ i : Fin 6, 0 < traceMoments i.castSucc := by
  intro i
  fin_cases i <;> norm_num [traceMoments]

theorem seventh_negative :
    traceMoments 6 = (-8593/823543 : ℝ) ∧ traceMoments 6 < 0 := by
  exact negative_moment_proved

theorem seven_times_sum :
    7*traceMoments 6 = 3*traceMoments 5 + 5*traceMoments 4 - 2*traceMoments 3 +
      3*traceMoments 2 - traceMoments 1 - traceMoments 0 := by
  change 7*(-8593/823543 : ℝ) = 3*(219766/117649) + 5*(5213/16807) -
    2*(6731/2401) + 3*(48/343) - 79/49 - 3/7
  norm_num

theorem printed_numerator :
    (659298 : ℤ)+182455-659638+49392-189679-50421 = -8593 := by
  norm_num

theorem printed_denominator : (7 : ℕ)^6 = 117649 := by
  norm_num

#print axioms seven_times_sum
#print axioms printed_numerator
#print axioms printed_denominator
#print axioms root_power_moments
#print axioms matrix_trace_moments
#print axioms first_six_positive
#print axioms seventh_negative
end NLA.IS03.MomentProse
