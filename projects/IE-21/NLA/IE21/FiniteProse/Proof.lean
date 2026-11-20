module

public import Mathlib.Tactic
public import NLA.IE21.FiniteSize
public import NLA.IE21.Covariance
public import NLA.IE21.AspectSchedule

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology RealInnerProductSpace
namespace NLA.IE21.FiniteProse

theorem actual_spherical_mgf (n : ℕ) (hn : 2 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (a : ℝ) (ha : |a| ≤ 1 / 8) :
    Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
    (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
      Real.exp (32 * a ^ 2) := by
  exact NLA.IE21.spherical_quadratic_mgf n hn x hx a ha

theorem actual_spherical_directional_tail (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1)
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) :
    (matrixLaw m n).real {A | s < |inner ℝ (covarianceOperator A x) x|} ≤
      2 * Real.exp (-(m : ℝ) * s ^ 2 / 128) := by
  exact NLA.IE21.directional_quadratic_tail_of_mgf m n hm (by omega) x hx
    (fun a ha => NLA.IE21.spherical_quadratic_mgf n hn x hx a ha) s hs

theorem actual_spherical_covariance_tail (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : 0 < t ∧ t ≤ 1) :
    (matrixLaw m n).real {A | covarianceError A > t} ≤
      2 * (9 : ℝ) ^ n * Real.exp (-(m : ℝ) * t ^ 2 / 512) := by
  exact NLA.IE21.covariance_concentration m n hm hn t ht

theorem actual_finite_joint_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n)
    (t ε δ : ℝ) (ht : 0 < t ∧ t < 1)
    (hε : 0 < ε ∧ ε ≤ (1 - θ) / 2) (hδ : 0 < δ ∧ δ < 1) :
    (matrixLaw m n).real {A | ¬(0 < operatorNorm A ∧
      |normalizedOperator A - 1| ≤ t ∧
      |normalizedDeletion θ A - gaussianTrim θ| ≤
        trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ)) ∧
      |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ m n t ε δ)} ≤
      finiteFailure m n t ε δ := by
  exact NLA.IE21.finite_size_bound θ hθ m n hm hn t ε δ ht hε hδ

theorem actual_aspect_parameter (m n : ℕ) :
    aspectParameter m n = 32 * Real.sqrt
      (Real.log ((m : ℝ) / n) / ((m : ℝ) / n)) := by
  rfl

theorem actual_failure_formula (m n : ℕ) (t ε δ : ℝ) :
    finiteFailure m n t ε δ =
      2 * (9 : ℝ)^n * Real.exp (-(m : ℝ)*t^2/512) +
      5 * (1 + 2/δ)^n * Real.exp (-2*(m : ℝ)*ε^2) := by
  rfl

theorem actual_finite_aspect_failure (m n : ℕ) (hn : 1 ≤ n)
    (hQ : 9 ≤ (m : ℝ) / n) (hlog : 1 ≤ Real.log ((m : ℝ) / n))
    (hd : aspectParameter m n ≤ 1) :
    finiteFailure m n (aspectParameter m n) (aspectParameter m n) (aspectParameter m n) ≤
      7 * Real.exp (-Real.log ((m : ℝ) / n)) := by
  exact NLA.IE21.finiteFailure_aspect_bound m n hn hQ hlog hd

theorem actual_aspect_schedule (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    (∀ᶠ j in atTop, 2 ≤ n j ∧ 0 < aspectParameter (m j) (n j) ∧
      aspectParameter (m j) (n j) < 1 ∧
      aspectParameter (m j) (n j) ≤ (1 - θ) / 2) ∧
    Tendsto (fun j => finiteFailure (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) ∧
    Tendsto (fun j => finiteRatioError θ (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) := by
  exact NLA.IE21.aspect_schedule θ hθ m n hm hn hnlim hQlim

#print axioms actual_spherical_mgf
#print axioms actual_spherical_directional_tail
#print axioms actual_spherical_covariance_tail
#print axioms actual_finite_joint_bound
#print axioms actual_aspect_parameter
#print axioms actual_failure_formula
#print axioms actual_finite_aspect_failure
#print axioms actual_aspect_schedule
end NLA.IE21.FiniteProse
