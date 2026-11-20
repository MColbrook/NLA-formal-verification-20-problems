module

public import NLA.IE22.GaussianPoincareHinge
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace NLA.IE22.LipschitzPoincare

/-- Lipschitz composition preserves finite Gaussian second moment even when
the function is not bounded or zero at the origin. -/
theorem lipschitz_memLp_gaussian {C : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith C f) :
    MemLp f 2 (gaussianReal 0 1) := by
  have hl : LipschitzWith C (fun x => f x - f 0) :=
    LipschitzWith.of_dist_le_mul fun x y => by simpa using hf.dist_le_mul x y
  have hh := hl.comp_memLp (by simp)
    (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by simp))
  have ha := hh.add (memLp_const (f 0))
  convert ha using 1
  ext x
  simp

/-- The scalar Gaussian Poincaré inequality for every Lipschitz function,
with the actual derivative. Differentiability and all integrability premises
are derived from Lipschitz continuity. -/
theorem scalar_gaussian_poincare {C : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith C f) :
    MemLp f 2 (gaussianReal 0 1) ∧
    (∀ᵐ x, HasDerivAt f (deriv f x) x) ∧
    Integrable (fun x => deriv f x ^ 2) (gaussianReal 0 1) ∧
    Var[f; gaussianReal 0 1] ≤ ∫ x, deriv f x ^ 2 ∂gaussianReal 0 1 := by
  have hm : Measurable (deriv f) := measurable_deriv f
  have hb (x : ℝ) : ‖deriv f x‖ ≤ C := norm_deriv_le_of_lipschitz hf
  have hder : ∀ᵐ x, HasDerivAt f (deriv f x) x :=
    hf.ae_differentiableAt_real.mono fun _ h => h.hasDerivAt
  have hLp : MemLp (deriv f) 2 (gaussianReal 0 1) :=
    MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hb)
  have hac (x y : ℝ) : AbsolutelyContinuousOnInterval f x y :=
    hf.lipschitzOnWith.absolutelyContinuousOnInterval
  have hi := interval_energy_of_absolutelyContinuous f (deriv f) hm C hb hder hac
  have hF := lipschitz_memLp_gaussian hf
  exact ⟨hF, hder, hLp.integrable_sq,
    gaussian_poincare_of_interval_energy f (deriv f) hF hm hLp.integrable_sq hi⟩

#print axioms scalar_gaussian_poincare
end NLA.IE22.LipschitzPoincare
