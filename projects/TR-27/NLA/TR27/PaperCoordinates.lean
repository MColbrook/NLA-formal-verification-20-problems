module

public import NLA.TR27.PaperCoordinateDefinitions
public import NLA.TR27.PaperIntegralIdentity
public import NLA.TR27.PaperQuotient
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem retainedIndex_ne_pivot (D : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    retainedIndex D hD j ≠ pivotIndex D hD := Fin.succAbove_ne _ _

theorem retainedIndex_val_ne_one (D : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    (retainedIndex D hD j).val ≠ 1 := by
  intro hj
  exact retainedIndex_ne_pivot D hD j (Fin.ext hj)

theorem chosen_center_coordinate (D r : ℕ) (i : Fin (D+1)) :
    projectionCenter D r (chosenParameters r) i =
      (if i.val = 1 then 1 else 0) - chosenPowerSum r i.val := by
  simp [projectionCenter, chosenParameters, tangentVector, curveVector,
    chosenPowerSum, Finset.sum_apply]

theorem chosen_center_pivot (D r : ℕ) (hD : 2 ≤ D) :
    projectionCenter D r (chosenParameters r) (pivotIndex D hD) = -chosenPivot r := by
  rw [chosen_center_coordinate]
  simp [pivotIndex, chosenPivot]

theorem chosen_center_retained (D r : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    projectionCenter D r (chosenParameters r) (retainedIndex D hD j) =
      -chosenPowerSum r (retainedIndex D hD j).val := by
  rw [chosen_center_coordinate, if_neg (retainedIndex_val_ne_one D hD j), zero_sub]

theorem coordinateProjection_center (D r : ℕ) (hD : 2 ≤ D) :
    coordinateProjection D r hD (projectionCenter D r (chosenParameters r)) = 0 := by
  ext j
  change chosenPivot r * _ - chosenPowerSum r _ * _ = 0
  rw [chosen_center_retained, chosen_center_pivot]
  ring

theorem coordinateProjection_surjective (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    Function.Surjective (coordinateProjection D r hD) := by
  intro v
  refine ⟨Fin.insertNth (pivotIndex D hD) 0 (fun j => v j / chosenPivot r), ?_⟩
  ext j
  simp [coordinateProjection, retainedIndex]
  field_simp [chosenPivot_ne_zero hr]

theorem coordinateProjection_kernel (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    LinearMap.ker (coordinateProjection D r hD) = centerLine D r (chosenParameters r) := by
  ext w
  rw [LinearMap.mem_ker]
  change coordinateProjection D r hD w = 0 ↔
    w ∈ Submodule.span ℂ {projectionCenter D r (chosenParameters r)}
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hw
    refine ⟨-w (pivotIndex D hD) / chosenPivot r, ?_⟩
    ext i
    by_cases hi : i = pivotIndex D hD
    · subst i
      simp [Pi.smul_apply, smul_eq_mul, chosen_center_pivot, chosenPivot_ne_zero hr]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      have hj := congrFun hw j
      change chosenPivot r * w (retainedIndex D hD j) -
        chosenPowerSum r (retainedIndex D hD j).val * w (pivotIndex D hD) = 0 at hj
      change (-w (pivotIndex D hD) / chosenPivot r) *
        projectionCenter D r (chosenParameters r) (retainedIndex D hD j) =
          w (retainedIndex D hD j)
      rw [chosen_center_retained]
      field_simp [chosenPivot_ne_zero hr]
      linear_combination -hj
  · rintro ⟨c, rfl⟩
    rw [map_smul, coordinateProjection_center, smul_zero]

noncomputable def quotientCoordinateEquiv (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    QuotientSpace D r (chosenParameters r) ≃ₗ[ℂ] (Fin D → ℂ) :=
  (Submodule.quotEquivOfEq _ _ (coordinateProjection_kernel D r hD hr).symm).trans
    ((coordinateProjection D r hD).quotKerEquivOfSurjective
      (coordinateProjection_surjective D r hD hr))

theorem quotientCoordinateEquiv_projection (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (w : CurveSpace D) :
    quotientCoordinateEquiv D r hD hr (quotientProjection D r (chosenParameters r) w) =
      coordinateProjection D r hD w := by
  rfl

#print axioms quotientCoordinateEquiv
end NLA.TR27.Paper
