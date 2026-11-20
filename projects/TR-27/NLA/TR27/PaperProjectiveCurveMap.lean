module

public import NLA.TR27.PaperProjectiveCompactness
public import NLA.TR27.PaperProjectiveCurveDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem projectiveCurveMap_mk (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    projectiveCurveMap D r hD hr (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (imageHomogeneousMap D r hD v)
        (fun h => hv ((imageHomogeneousMap_eq_zero_iff D r hD hr v).mp h)) := by
  obtain ⟨c,hc,heq⟩ := represents_mk v hv
  unfold projectiveCurveMap
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨c^D, ?_⟩
  rw [heq, imageHomogeneousMap_smul]

theorem continuous_imageHomogeneousMap (D r : ℕ) (hD : 2 ≤ D) :
    Continuous (imageHomogeneousMap D r hD) := by
  apply continuous_pi
  intro j
  simp only [imageHomogeneousMap_apply]
  fun_prop

theorem continuous_projectiveCurveMap (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    Continuous (projectiveCurveMap D r hD hr) := by
  apply continuous_coinduced_dom.mpr
  let F : {v : Fin 2 → ℂ // v ≠ 0} → {v : Fin D → ℂ // v ≠ 0} :=
    fun v => ⟨imageHomogeneousMap D r hD v.val,
      fun h => v.property ((imageHomogeneousMap_eq_zero_iff D r hD hr v.val).mp h)⟩
  have hF : Continuous F :=
    ((continuous_imageHomogeneousMap D r hD).comp continuous_subtype_val).subtype_mk _
  have h := (continuous_coordinate_projective_mk D).comp hF
  convert h using 1
  funext v
  exact projectiveCurveMap_mk D r hD hr v.val v.property

theorem projectiveCurveMap_compact_range (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    IsCompact (Set.range (projectiveCurveMap D r hD hr)) := by
  letI := coordinateProjective_compact 2
  exact isCompact_range (continuous_projectiveCurveMap D r hD hr)

#print axioms continuous_projectiveCurveMap
#print axioms projectiveCurveMap_compact_range
end NLA.TR27.Paper
