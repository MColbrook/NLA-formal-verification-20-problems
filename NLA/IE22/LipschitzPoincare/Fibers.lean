module

public import NLA.IE22.LipschitzPoincare.Gradient
public import NLA.IE22.LipschitzPoincare.Resampling

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE22.LipschitzPoincare
open NLA.IE21

theorem coordinate_update_formula {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    WithLp.toLp 2 (Function.update x i t) = (WithLp.toLp 2 x : Space d) +
      (t - x i) • EuclideanSpace.basisFun (Fin d) ℝ i := by
  classical
  ext j
  by_cases h : j = i
  · subst j
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  · simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, h, Ne.symm h]

theorem coordinate_update_hasDerivAt {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    HasDerivAt (fun s => (WithLp.toLp 2 (Function.update x i s) : Space d))
      (EuclideanSpace.basisFun (Fin d) ℝ i) t := by
  simp_rw [coordinate_update_formula]
  simpa using (((hasDerivAt_id t).sub_const (x i)).smul_const
    (EuclideanSpace.basisFun (Fin d) ℝ i)).const_add (WithLp.toLp 2 x : Space d)

theorem coordinate_update_lipschitz {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    LipschitzWith 1 (fun s => (WithLp.toLp 2 (Function.update x i s) : Space d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  have he : (WithLp.toLp 2 (Function.update x i s) : Space d) -
      WithLp.toLp 2 (Function.update x i t) =
      (s-t) • EuclideanSpace.basisFun (Fin d) ℝ i := by
    rw [coordinate_update_formula, coordinate_update_formula]
    module
  rw [dist_eq_norm, he, norm_smul, (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one]
  simp [Real.dist_eq]

theorem coordinate_fiber_derivative {d : ℕ} (f : Space d → ℝ)
    (x : Fin d → ℝ) (i : Fin d) (t : ℝ)
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (Function.update x i t))) :
    deriv (fun s => f (WithLp.toLp 2 (Function.update x i s))) t =
      gradient f (WithLp.toLp 2 (Function.update x i t)) i := by
  rw [gradient_coordinate]
  exact (hf.hasFDerivAt.comp_hasDerivAt t (coordinate_update_hasDerivAt x i t)).deriv

theorem coordinate_fiber_lipschitz {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) (x : Fin d → ℝ) (i : Fin d) :
    LipschitzWith C (fun s => f (WithLp.toLp 2 (Function.update x i s))) := by
  simpa only [mul_one, Function.comp_def] using hf.comp (coordinate_update_lipschitz x i)

#print axioms coordinate_fiber_derivative
end NLA.IE22.LipschitzPoincare
