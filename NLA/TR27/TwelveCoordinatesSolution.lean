module

public import NLA.TR27.PaperTwelveCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem paper_twelve_power_sum (j : ℕ) : chosenPowerSum 3 j = 1+2^j+3^j := by
  exact twelve_power_sum j

theorem paper_twelve_pivot : chosenPivot 3 = 5 := by
  exact twelve_pivot

theorem paper_twelve_projection (w : CurveSpace 12) (j : Fin 12) :
    coordinateProjection 12 3 (by omega) w j =
      5*w (retainedIndex 12 (by omega) j) -
        (1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val)*w 1 := by
  exact twelve_projection w j

theorem paper_twelve_retained_columns (j : Fin 12) :
    coordinateProjection 12 3 (by omega)
      (Pi.single (retainedIndex 12 (by omega) j) 1) = 5 • Pi.single j 1 := by
  exact twelve_retained_columns j

theorem paper_twelve_projection_quotient :
    Function.Surjective (coordinateProjection 12 3 (by omega)) ∧
      LinearMap.ker (coordinateProjection 12 3 (by omega)) =
        centerLine 12 3 (chosenParameters 3) ∧
      projectionCenter 12 3 (chosenParameters 3) 1 = -5 := by
  exact twelve_projection_quotient

theorem paper_twelve_homogeneous (s t : ℂ) (j : Fin 12) :
    imageHomogeneousMap 12 3 (by omega) ![s,t] j =
      5*s^(12-(retainedIndex 12 (by omega) j).val)*t^(retainedIndex 12 (by omega) j).val -
      (1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val)*s^11*t := by
  exact twelve_homogeneous s t j

theorem paper_twelve_no_basepoint_values :
    (∀ t : ℂ, imageHomogeneousMap 12 3 (by omega) ![0,t] 11 = 5*t^12) ∧
      (∀ t : ℂ, coordinateCurve 12 3 (by omega) (some t) 0 = 5-3*t) ∧
      coordinateCurve 12 3 (by omega) (some (5/3)) 1 = -85/9 := by
  exact twelve_no_basepoint_values

theorem paper_twelve_tangent_entries (j : Fin 12) :
    coordinateTangent 12 3 (by omega) j =
      -(1+2^(retainedIndex 12 (by omega) j).val+3^(retainedIndex 12 (by omega) j).val) := by
  exact twelve_tangent_entries j

theorem paper_twelve_three_terms :
    coordinateCurve 12 3 (by omega) (some 1) +
      coordinateCurve 12 3 (by omega) (some 2) +
      coordinateCurve 12 3 (by omega) (some 3) = coordinateTangent 12 3 (by omega) := by
  exact twelve_three_terms

theorem paper_twelve_tangent_derivative :
    HasDerivAt (fun t : ℂ => coordinateCurve 12 3 (by omega) (some t))
      (coordinateTangent 12 3 (by omega)) 0 := by
  exact twelve_tangent_derivative

theorem paper_twelve_nine_terms :
    PiTensorProduct.tprod ℂ (fun _ : Fin 2 => coordinateTangent 12 3 (by omega)) =
      ∑ a : Fin 2 → Fin 3, PiTensorProduct.tprod ℂ
        (fun i => coordinateCurve 12 3 (by omega) (some (((a i).val+1 : ℕ) : ℂ))) := by
  exact twelve_nine_terms

#print axioms paper_twelve_power_sum
#print axioms paper_twelve_pivot
#print axioms paper_twelve_projection
#print axioms paper_twelve_retained_columns
#print axioms paper_twelve_projection_quotient
#print axioms paper_twelve_homogeneous
#print axioms paper_twelve_no_basepoint_values
#print axioms paper_twelve_tangent_entries
#print axioms paper_twelve_three_terms
#print axioms paper_twelve_tangent_derivative
#print axioms paper_twelve_nine_terms

end NLA.TR27.Paper
