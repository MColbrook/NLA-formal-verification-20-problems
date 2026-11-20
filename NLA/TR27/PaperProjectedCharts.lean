module

public import NLA.TR27.PaperTangentGeometry
public import NLA.TR27.PaperImageGeometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace NLA.TR27.Paper

theorem independent_vectors_ratio_minor {n : ℕ} (w v : Fin n → ℂ)
    (hi : ∀ α β : ℂ, α • w + β • v = 0 → α = 0 ∧ β = 0) :
    ∃ i j : Fin n, w i ≠ 0 ∧ v j * w i - w j * v i ≠ 0 := by
  have hw : w ≠ 0 := by
    intro h
    have hz := hi 1 0 (by simp [h])
    exact one_ne_zero hz.1
  obtain ⟨i, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (funext h)
  by_contra h
  push Not at h
  have hm (j : Fin n) : v j * w i - w j * v i = 0 := h i j hi0
  have heq : (-v i / w i) • w + (1 : ℂ) • v = 0 := by
    ext j
    change (-v i / w i)*w j + 1*v j = 0
    field_simp [hi0]
    linear_combination hm j
  exact one_ne_zero (hi _ _ heq).2

theorem normalized_chart_has_nonzero_derivative {n : ℕ}
    (f : ℂ → Fin n → ℂ) (v : Fin n → ℂ) (a : ℂ) (hf : HasDerivAt f v a)
    (hi : ∀ α β : ℂ, α • f a + β • v = 0 → α = 0 ∧ β = 0) :
    ∃ i j : Fin n, f a i ≠ 0 ∧ ∃ d : ℂ, d ≠ 0 ∧
      HasDerivAt (fun t => f t j / f t i) d a := by
  obtain ⟨i,j,hwi,hm⟩ := independent_vectors_ratio_minor (f a) v hi
  refine ⟨i,j,hwi,(v j*f a i - f a j*v i)/(f a i)^2,
    div_ne_zero hm (pow_ne_zero _ hwi), ?_⟩
  exact (hasDerivAt_pi.mp hf j).div (hasDerivAt_pi.mp hf i) hwi

theorem coordinate_curve_tangent_coefficients_eq_zero (D r : ℕ) (hD : 2 ≤ D)
    (hr : 3 ≤ r) (hgap : 2*(r+1) ≤ D) (t : Option ℂ) (α β : ℂ)
    (h : α • coordinateCurve D r hD t +
      β • coordinateProjection D r hD (curveTangent D t) = 0) : α = 0 ∧ β = 0 := by
  have ha : Function.Injective (fun i : Fin r => ((i.val+1 : ℕ) : ℂ)) := by
    intro i j hij
    apply chosenParameters_injective r
    exact congrArg some hij
  have ha0 : ∀ i : Fin r, ((i.val+1 : ℕ) : ℂ) ≠ 0 := by
    intro i
    exact_mod_cast Nat.succ_ne_zero i.val
  apply projected_curve_tangent_coefficients_eq_zero (by omega) hgap _ ha ha0 t α β
  change α • quotientCurve D r (chosenParameters r) t +
    β • quotientProjection D r (chosenParameters r) (curveTangent D t) = 0
  apply (quotientCoordinateEquiv D r hD hr).injective
  simp only [map_add, map_smul, map_zero, quotientCurve, quotientCoordinateEquiv_projection]
  exact h

theorem coordinateCurve_hasDerivAt (D r : ℕ) (hD : 2 ≤ D) (a : ℂ) :
    HasDerivAt (fun t => coordinateCurve D r hD (some t))
      (coordinateProjection D r hD (curveTangent D (some a))) a := by
  let P : CurveSpace D →L[ℂ] (Fin D → ℂ) := (coordinateProjection D r hD).toContinuousLinearMap
  exact P.hasFDerivAt.comp_hasDerivAt a (curveVector_hasDerivAt D a)

theorem projectedInfinity_hasDerivAt (D r : ℕ) (hD : 2 ≤ D) :
    HasDerivAt (fun t => coordinateProjection D r hD (infinityChart D t))
      (coordinateProjection D r hD (curveTangent D none)) 0 := by
  let P : CurveSpace D →L[ℂ] (Fin D → ℂ) := (coordinateProjection D r hD).toContinuousLinearMap
  exact P.hasFDerivAt.comp_hasDerivAt 0 (infinityChart_hasDerivAt D)

theorem finite_projective_chart_nonzero_derivative (D r : ℕ) (hD : 2 ≤ D)
    (hr : 3 ≤ r) (hgap : 2*(r+1) ≤ D) (a : ℂ) :
    ∃ i j : Fin D, coordinateCurve D r hD (some a) i ≠ 0 ∧
      ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt
        (fun t => coordinateCurve D r hD (some t) j / coordinateCurve D r hD (some t) i) d a := by
  exact normalized_chart_has_nonzero_derivative _ _ a (coordinateCurve_hasDerivAt D r hD a)
    (coordinate_curve_tangent_coefficients_eq_zero D r hD hr hgap (some a))

theorem infinity_projective_chart_nonzero_derivative (D r : ℕ) (hD : 2 ≤ D)
    (hr : 3 ≤ r) (hgap : 2*(r+1) ≤ D) :
    ∃ i j : Fin D, coordinateCurve D r hD none i ≠ 0 ∧
      ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt
        (fun t => coordinateProjection D r hD (infinityChart D t) j /
          coordinateProjection D r hD (infinityChart D t) i) d 0 := by
  have h := normalized_chart_has_nonzero_derivative _ _ 0 (projectedInfinity_hasDerivAt D r hD) ?_
  · simpa only [infinityChart_zero, coordinateCurve] using h
  · rw [infinityChart_zero]
    exact coordinate_curve_tangent_coefficients_eq_zero D r hD hr hgap none

#print axioms finite_projective_chart_nonzero_derivative
#print axioms infinity_projective_chart_nonzero_derivative
end NLA.TR27.Paper
