module

public import NLA.TR27.ArbitraryGeometryDefinitions
public import NLA.TR27.PaperQuotient

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem parameter_center_zero (D r : ℕ) (a : Fin r → ℂ) :
    projectionCenter D r (fun i => some (a i)) 0 = -(r : ℂ) := by
  simp [projectionCenter, tangentVector, curveVector, Finset.sum_apply]

theorem parameterProjection_center (D r : ℕ) (a : Fin r → ℂ) :
    parameterProjection D r a (projectionCenter D r (fun i => some (a i))) = 0 := by
  ext j
  change (r : ℂ)*_ + _*_ = 0
  rw [parameter_center_zero]
  ring

theorem parameterProjection_surjective (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ) :
    Function.Surjective (parameterProjection D r a) := by
  intro v
  refine ⟨Fin.cases 0 (fun j => v j / (r : ℂ)), ?_⟩
  ext j
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [parameterProjection, hr0]
  field_simp [hr0]
  <;> ring

theorem parameterProjection_kernel (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ) :
    LinearMap.ker (parameterProjection D r a) = centerLine D r (fun i => some (a i)) := by
  ext w
  rw [LinearMap.mem_ker]
  change parameterProjection D r a w = 0 ↔
    w ∈ Submodule.span ℂ {projectionCenter D r (fun i => some (a i))}
  rw [Submodule.mem_span_singleton]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  constructor
  · intro hw
    refine ⟨-w 0/(r : ℂ), ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.smul_apply, smul_eq_mul, parameter_center_zero, hr0]
    · have hj := congrFun hw j
      change (r : ℂ)*w j.succ +
        projectionCenter D r (fun i => some (a i)) j.succ*w 0 = 0 at hj
      change (-w 0/(r : ℂ))*projectionCenter D r (fun i => some (a i)) j.succ = w j.succ
      field_simp [hr0]
      linear_combination -hj
  · rintro ⟨c,rfl⟩
    rw [map_smul, parameterProjection_center, smul_zero]

def parameterCoordinateEquiv (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ) :
    QuotientSpace D r (fun i => some (a i)) ≃ₗ[ℂ] (Fin D → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (parameterProjection_kernel D r hr a).symm).trans
    ((parameterProjection D r a).quotKerEquivOfSurjective
      (parameterProjection_surjective D r hr a))

theorem parameterCoordinateEquiv_projection (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ)
    (w : CurveSpace D) :
    parameterCoordinateEquiv D r hr a (quotientProjection D r (fun i => some (a i)) w) =
      parameterProjection D r a w := by
  rfl

theorem parameterCoordinateCurve_nonzero (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (t : Option ℂ) :
    parameterCoordinateCurve D r a t ≠ 0 := by
  change parameterCoordinateEquiv D r hr a (quotientCurve D r (fun i => some (a i)) t) ≠ 0
  exact (parameterCoordinateEquiv D r hr a).map_ne_zero_iff.mpr
    (quotient_curve_nonzero hD hgap _ t)

#print axioms parameterCoordinateEquiv
end NLA.TR27.Paper
