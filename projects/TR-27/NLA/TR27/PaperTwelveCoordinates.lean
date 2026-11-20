module

public import NLA.TR27.PaperCoordinates
public import NLA.TR27.PaperHomogeneous
public import NLA.TR27.PaperQuotientRank
public import NLA.TR27.PaperProjectedCharts

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem twelve_power_sum (j : ℕ) : chosenPowerSum 3 j = 1+2^j+3^j := by
  simp [chosenPowerSum, Fin.sum_univ_succ]
  ring

theorem twelve_pivot : chosenPivot 3 = 5 := by
  norm_num [chosenPivot, twelve_power_sum]

theorem twelve_projection (w : CurveSpace 12) (j : Fin 12) :
    coordinateProjection 12 3 (by omega) w j =
      5*w (retainedIndex 12 (by omega) j) -
        (1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val)*w 1 := by
  simp [coordinateProjection, twelve_pivot, twelve_power_sum, pivotIndex]

theorem twelve_retained_columns (j : Fin 12) :
    coordinateProjection 12 3 (by omega)
      (Pi.single (retainedIndex 12 (by omega) j) 1) = 5 • Pi.single j 1 := by
  ext i
  rw [twelve_projection]
  have hj := retainedIndex_ne_pivot 12 (by omega) j
  have hji : (retainedIndex 12 (by omega) j) ≠ (1 : Fin 13) := hj
  simp only [Pi.single_apply, if_neg (Ne.symm hji), Pi.smul_apply, smul_eq_mul,
    mul_zero, sub_zero]
  simp [retainedIndex, Fin.succAbove_right_injective.eq_iff]

theorem twelve_projection_quotient :
    Function.Surjective (coordinateProjection 12 3 (by omega)) ∧
      LinearMap.ker (coordinateProjection 12 3 (by omega)) =
        centerLine 12 3 (chosenParameters 3) ∧
      projectionCenter 12 3 (chosenParameters 3) 1 = -5 := by
  refine ⟨coordinateProjection_surjective 12 3 (by omega) (by omega),
    coordinateProjection_kernel 12 3 (by omega) (by omega), ?_⟩
  norm_num [chosen_center_coordinate, twelve_power_sum]

theorem twelve_homogeneous (s t : ℂ) (j : Fin 12) :
    imageHomogeneousMap 12 3 (by omega) ![s,t] j =
      5*s^(12-(retainedIndex 12 (by omega) j).val)*t^(retainedIndex 12 (by omega) j).val -
      (1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val)*s^11*t := by
  rw [imageHomogeneousMap_apply, twelve_pivot, twelve_power_sum]
  rfl

theorem twelve_no_basepoint_values :
    (∀ t : ℂ, imageHomogeneousMap 12 3 (by omega) ![0,t] 11 = 5*t^12) ∧
      (∀ t : ℂ, coordinateCurve 12 3 (by omega) (some t) 0 = 5-3*t) ∧
      coordinateCurve 12 3 (by omega) (some (5/3)) 1 = -85/9 := by
  constructor
  · intro t
    simpa [imageLastIndex, twelve_pivot] using imageHomogeneousMap_last 12 3 (by omega) ![0,t]
  constructor
  · intro t
    change coordinateProjection 12 3 (by omega) (curveVector 12 (some t)) 0 = _
    rw [twelve_projection]
    norm_num [curveVector, retainedIndex, pivotIndex, Fin.succAbove]
  · change coordinateProjection 12 3 (by omega) (curveVector 12 (some (5/3))) 1 = _
    rw [twelve_projection]
    norm_num [curveVector, retainedIndex, pivotIndex, Fin.succAbove]

theorem twelve_tangent_entries (j : Fin 12) :
    coordinateTangent 12 3 (by omega) j =
      -(1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val) := by
  have hj := retainedIndex_val_ne_one 12 (by omega) j
  simp [coordinateTangent, twelve_projection, tangentVector, hj]

theorem twelve_three_terms :
    coordinateCurve 12 3 (by omega) (some 1) +
      coordinateCurve 12 3 (by omega) (some 2) +
      coordinateCurve 12 3 (by omega) (some 3) = coordinateTangent 12 3 (by omega) := by
  have h := congrArg (quotientCoordinateEquiv 12 3 (by omega) (by omega))
    (quotient_tangent_sum 12 3 (chosenParameters 3))
  simp only [quotientTangent, quotientCurve, map_sum, quotientCoordinateEquiv_projection] at h
  norm_num [chosenParameters, Fin.sum_univ_succ, coordinateCurve, coordinateTangent, add_assoc] at h ⊢
  exact h.symm

theorem twelve_tangent_derivative :
    HasDerivAt (fun t : ℂ => coordinateCurve 12 3 (by omega) (some t))
      (coordinateTangent 12 3 (by omega)) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  have hj := retainedIndex_val_ne_one 12 (by omega) j
  have hpow := (hasDerivAt_id (0 : ℂ)).pow (retainedIndex 12 (by omega) j).val
  have h := (hpow.const_mul 5).sub
    ((hasDerivAt_id (0 : ℂ)).const_mul
      (1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val))
  have hzero : (retainedIndex 12 (by omega) j).val *
      (0 : ℂ)^((retainedIndex 12 (by omega) j).val-1) = 0 := by
    by_cases hz : (retainedIndex 12 (by omega) j).val = 0
    · simp [hz]
    · have hp : (retainedIndex 12 (by omega) j).val-1 ≠ 0 := by omega
      simp [hp]
  convert h using 1 <;>
    simp [coordinateCurve, twelve_projection, curveVector, twelve_tangent_entries, hzero,
      Pi.sub_def]

theorem twelve_nine_terms :
    PiTensorProduct.tprod ℂ (fun _ : Fin 2 => coordinateTangent 12 3 (by omega)) =
      ∑ a : Fin 2 → Fin 3, PiTensorProduct.tprod ℂ
        (fun i => coordinateCurve 12 3 (by omega) (some (((a i).val+1 : ℕ) : ℂ))) := by
  have h : coordinateTangent 12 3 (by omega) =
      ∑ a : Fin 3, coordinateCurve 12 3 (by omega) (some ((a.val+1 : ℕ) : ℂ)) := by
    have hs := twelve_three_terms.symm
    norm_num [Fin.sum_univ_succ, add_assoc] at hs ⊢
    exact hs
  simp_rw [h]
  exact MultilinearMap.map_sum _ _

#print axioms twelve_nine_terms
#print axioms twelve_tangent_derivative
#print axioms twelve_no_basepoint_values
end NLA.TR27.Paper
