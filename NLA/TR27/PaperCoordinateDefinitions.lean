module

public import NLA.TR27.PaperProjectionDefinitions
public import NLA.TR27.PaperIntegralDefinitions
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def pivotIndex (D : ℕ) (hD : 2 ≤ D) : Fin (D+1) := ⟨1, by omega⟩

/-- Source coordinates 0,2,...,D, in their original order. -/
def retainedIndex (D : ℕ) (hD : 2 ≤ D) : Fin D → Fin (D+1) :=
  (pivotIndex D hD).succAbove

def coordinateProjection (D r : ℕ) (hD : 2 ≤ D) : CurveSpace D →ₗ[ℂ] (Fin D → ℂ) where
  toFun w j := chosenPivot r * w (retainedIndex D hD j) -
    chosenPowerSum r (retainedIndex D hD j).val * w (pivotIndex D hD)
  map_add' u v := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c w := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def coordinateCurve (D r : ℕ) (hD : 2 ≤ D) (t : Option ℂ) : Fin D → ℂ :=
  coordinateProjection D r hD (curveVector D t)

def coordinateTangent (D r : ℕ) (hD : 2 ≤ D) : Fin D → ℂ :=
  coordinateProjection D r hD (tangentVector D)

end NLA.TR27.Paper
