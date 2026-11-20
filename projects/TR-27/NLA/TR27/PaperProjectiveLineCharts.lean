module

public import NLA.TR27.PaperProjectiveEmbedding
public import NLA.TR27.PaperProjectiveCharts
public import NLA.TR27.PaperTangentGeometryDefinitions
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

/-- The two standard scalar charts on the complex projective line. -/
def projectiveLineChart (i : Fin 2) : OpenPartialHomeomorph (ℙ ℂ (Fin 2 → ℂ)) ℂ :=
  (coordinateProjectiveChart i).trans (Homeomorph.funUnique (Fin 1) ℂ).toOpenPartialHomeomorph

theorem projectiveLineChart_target (i : Fin 2) : (projectiveLineChart i).target = Set.univ := by
  ext t
  simp [projectiveLineChart, coordinateProjectiveChart]

theorem projectiveLineChart_source (i : Fin 2) :
    (projectiveLineChart i).source = {p | p.rep i ≠ 0} := by
  ext p
  simp [projectiveLineChart, coordinateProjectiveChart]

theorem projectiveLineChart_inverse_isOpenEmbedding (i : Fin 2) :
    Topology.IsOpenEmbedding (projectiveLineChart i).symm :=
  (projectiveLineChart i).symm.isOpenEmbedding (projectiveLineChart_target i)

theorem projectiveLineChart_zero_inverse (t : ℂ) :
    (projectiveLineChart 0).symm t = projectiveLinePoint (some t) := by
  change Projectivization.mk ℂ (Fin.insertNth (0 : Fin 2) 1 (fun _ : Fin 1 => t)) _ =
    Projectivization.mk ℂ (![1,t]) _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [Fin.insertNth, Fin.succAboveCases]

theorem projectiveLineChart_one_inverse (t : ℂ) :
    (projectiveLineChart 1).symm t = Projectivization.mk ℂ (![t,1]) (by simp) := by
  change Projectivization.mk ℂ (Fin.insertNth (1 : Fin 2) (1 : ℂ)
    (fun _ : Fin 1 => t) : Fin 2 → ℂ) _ = _
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  ext i
  fin_cases i <;> simp [Fin.insertNth, Fin.succAboveCases]

theorem imageHomogeneousMap_reverse_chart (D r : ℕ) (hD : 2 ≤ D) (t : ℂ) :
    imageHomogeneousMap D r hD (![t,1]) = coordinateProjection D r hD (infinityChart D t) := by
  ext j
  simp [imageHomogeneousMap_apply, coordinateProjection, infinityChart, pivotIndex]

theorem projectiveCurveMap_reverse_chart_rep (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) (t : ℂ) :
    Represents (coordinateProjection D r hD (infinityChart D t))
      (projectiveCurveMap D r hD hr ((projectiveLineChart 1).symm t)) := by
  rw [projectiveLineChart_one_inverse, projectiveCurveMap_mk]
  have h := represents_mk (imageHomogeneousMap D r hD (![t,1]))
    (fun hz => (by simp : (![t,1] : Fin 2 → ℂ) ≠ 0)
      ((imageHomogeneousMap_eq_zero_iff D r hD hr _).mp hz))
  simpa only [imageHomogeneousMap_reverse_chart] using h

theorem projectiveCoordinateRatio_of_represents {n : ℕ} (i j : Fin n) (v : Fin n → ℂ)
    (p : ℙ ℂ (Fin n → ℂ)) (hp : Represents v p) :
    projectiveCoordinateRatio i j p = v j / v i := by
  obtain ⟨c,hc,heq⟩ := hp
  rw [projectiveCoordinateRatio, heq]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc

theorem finite_chart_curve_ratio (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) (i j : Fin D) (t : ℂ) :
    projectiveCoordinateRatio i j
      (projectiveCurveMap D r hD hr ((projectiveLineChart 0).symm t)) =
        coordinateCurve D r hD (some t) j / coordinateCurve D r hD (some t) i := by
  rw [projectiveLineChart_zero_inverse]
  exact projectiveCoordinateRatio_of_represents i j _ _ (projectiveCurveMap_parameter_rep D r hD hr (some t))

theorem infinity_chart_curve_ratio (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) (i j : Fin D) (t : ℂ) :
    projectiveCoordinateRatio i j
      (projectiveCurveMap D r hD hr ((projectiveLineChart 1).symm t)) =
        coordinateProjection D r hD (infinityChart D t) j /
          coordinateProjection D r hD (infinityChart D t) i :=
  projectiveCoordinateRatio_of_represents i j _ _ (projectiveCurveMap_reverse_chart_rep D r hD hr t)

#print axioms finite_chart_curve_ratio
#print axioms infinity_chart_curve_ratio
end NLA.TR27.Paper
