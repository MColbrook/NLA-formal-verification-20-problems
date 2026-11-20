module

public import NLA.TR27.PaperProjectedCharts
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology
open Filter
namespace NLA.TR27.Paper

theorem coordinateCurve_coordinate_analytic (D r : ℕ) (hD : 2 ≤ D)
    (a : ℂ) (j : Fin D) :
    AnalyticAt ℂ (fun t => coordinateCurve D r hD (some t) j) a := by
  change AnalyticAt ℂ (fun t => chosenPivot r * t^(retainedIndex D hD j).val -
    chosenPowerSum r (retainedIndex D hD j).val * t^((pivotIndex D hD).val)) a
  exact (analyticAt_const.mul (analyticAt_id.pow _)).sub
    (analyticAt_const.mul (analyticAt_id.pow _))

theorem projectedInfinity_coordinate_analytic (D r : ℕ) (hD : 2 ≤ D)
    (a : ℂ) (j : Fin D) :
    AnalyticAt ℂ (fun t => coordinateProjection D r hD (infinityChart D t) j) a := by
  change AnalyticAt ℂ (fun t => chosenPivot r * t^(D-(retainedIndex D hD j).val) -
    chosenPowerSum r (retainedIndex D hD j).val * t^(D-(pivotIndex D hD).val)) a
  exact (analyticAt_const.mul (analyticAt_id.pow _)).sub
    (analyticAt_const.mul (analyticAt_id.pow _))

/-- A nonzero derivative of an actual coordinate ratio supplies an analytic
local inverse and analytic coordinate graphs. This describes a local branch;
the global embedding argument must additionally exclude other branches. -/
theorem normalized_chart_analytic_inverse {n : ℕ} (f : ℂ → Fin n → ℂ) (a : ℂ)
    (ha : ∀ k, AnalyticAt ℂ (fun t => f t k) a) (i j : Fin n) (hi : f a i ≠ 0)
    (d : ℂ) (hd : d ≠ 0) (hf : HasDerivAt (fun t => f t j / f t i) d a) :
    ∃ g : ℂ → ℂ,
      g (f a j / f a i) = a ∧
      AnalyticAt ℂ g (f a j / f a i) ∧
      (∀ᶠ t in 𝓝 a, g (f t j / f t i) = t) ∧
      (∀ᶠ z in 𝓝 (f a j / f a i), f (g z) j / f (g z) i = z) ∧
      (∀ k, AnalyticAt ℂ (fun z => f (g z) k / f (g z) i) (f a j / f a i)) := by
  let F : ℂ → ℂ := fun t => f t j / f t i
  have hF : AnalyticAt ℂ F a := (ha j).div (ha i) hi
  have hF' : deriv F a ≠ 0 := by rwa [hf.deriv]
  let g := hF.hasStrictDerivAt.localInverse F (deriv F a) a hF'
  have hleft : ∀ᶠ t in 𝓝 a, g (F t) = t :=
    hF.hasStrictDerivAt.eventually_left_inverse hF'
  have hval : g (F a) = a := hleft.self_of_nhds
  have hg : AnalyticAt ℂ g (F a) := hF.analyticAt_localInverse hF'
  refine ⟨g,hval,hg,hleft,hF.hasStrictDerivAt.eventually_right_inverse hF', ?_⟩
  intro k
  have hk : AnalyticAt ℂ (fun t => f t k / f t i) a := (ha k).div (ha i) hi
  rw [← hval] at hk
  exact hk.comp hg

theorem finite_projective_analytic_chart (D r : ℕ) (hD : 2 ≤ D)
    (hr : 3 ≤ r) (hgap : 2*(r+1) ≤ D) (a : ℂ) :
    ∃ i j : Fin D, coordinateCurve D r hD (some a) i ≠ 0 ∧
      ∃ g : ℂ → ℂ,
        g (coordinateCurve D r hD (some a) j / coordinateCurve D r hD (some a) i) = a ∧
        AnalyticAt ℂ g (coordinateCurve D r hD (some a) j / coordinateCurve D r hD (some a) i) ∧
        (∀ᶠ t in 𝓝 a, g (coordinateCurve D r hD (some t) j / coordinateCurve D r hD (some t) i) = t) ∧
        (∀ᶠ z in 𝓝 (coordinateCurve D r hD (some a) j / coordinateCurve D r hD (some a) i),
          coordinateCurve D r hD (some (g z)) j / coordinateCurve D r hD (some (g z)) i = z) ∧
        (∀ k, AnalyticAt ℂ (fun z => coordinateCurve D r hD (some (g z)) k /
          coordinateCurve D r hD (some (g z)) i)
            (coordinateCurve D r hD (some a) j / coordinateCurve D r hD (some a) i)) := by
  obtain ⟨i,j,hi,d,hd,hf⟩ := finite_projective_chart_nonzero_derivative D r hD hr hgap a
  exact ⟨i,j,hi,normalized_chart_analytic_inverse _ a
    (coordinateCurve_coordinate_analytic D r hD a) i j hi d hd hf⟩

theorem infinity_projective_analytic_chart (D r : ℕ) (hD : 2 ≤ D)
    (hr : 3 ≤ r) (hgap : 2*(r+1) ≤ D) :
    let f := fun t => coordinateProjection D r hD (infinityChart D t)
    ∃ i j : Fin D, f 0 i ≠ 0 ∧ ∃ g : ℂ → ℂ,
      g (f 0 j / f 0 i) = 0 ∧
      AnalyticAt ℂ g (f 0 j / f 0 i) ∧
      (∀ᶠ t in 𝓝 0, g (f t j / f t i) = t) ∧
      (∀ᶠ z in 𝓝 (f 0 j / f 0 i), f (g z) j / f (g z) i = z) ∧
      (∀ k, AnalyticAt ℂ (fun z => f (g z) k / f (g z) i) (f 0 j / f 0 i)) := by
  obtain ⟨i,j,hi,d,hd,hf⟩ := infinity_projective_chart_nonzero_derivative D r hD hr hgap
  have hi' : coordinateProjection D r hD (infinityChart D 0) i ≠ 0 := by
    simpa only [infinityChart_zero, coordinateCurve] using hi
  exact ⟨i,j,hi',normalized_chart_analytic_inverse _ 0
    (projectedInfinity_coordinate_analytic D r hD 0) i j hi' d hd hf⟩

#print axioms finite_projective_analytic_chart
#print axioms infinity_projective_analytic_chart
end NLA.TR27.Paper
