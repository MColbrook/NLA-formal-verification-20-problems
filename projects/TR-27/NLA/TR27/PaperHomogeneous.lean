module

public import NLA.TR27.PaperHomogeneousDefinitions
public import NLA.TR27.PaperCoordinates
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

def imageZeroIndex (D : ℕ) (hD : 2 ≤ D) : Fin D := ⟨0, by omega⟩
def imageTwoIndex (D : ℕ) (hD : 2 ≤ D) : Fin D := ⟨1, by omega⟩
def imageLastIndex (D : ℕ) (hD : 2 ≤ D) : Fin D := ⟨D-1, by omega⟩

@[simp] theorem retainedIndex_zero (D : ℕ) (hD : 2 ≤ D) :
    (retainedIndex D hD (imageZeroIndex D hD)).val = 0 := by
  simp [retainedIndex, pivotIndex, imageZeroIndex, Fin.succAbove, Fin.lt_def]

@[simp] theorem retainedIndex_two (D : ℕ) (hD : 2 ≤ D) :
    (retainedIndex D hD (imageTwoIndex D hD)).val = 2 := by
  simp [retainedIndex, pivotIndex, imageTwoIndex, Fin.succAbove, Fin.lt_def]

@[simp] theorem retainedIndex_last (D : ℕ) (hD : 2 ≤ D) :
    (retainedIndex D hD (imageLastIndex D hD)).val = D := by
  have h : ¬ D-1 < 1 := by omega
  simp [retainedIndex, pivotIndex, imageLastIndex, Fin.succAbove, Fin.lt_def, h]
  omega

@[simp] theorem chosenPowerSum_zero (r : ℕ) : chosenPowerSum r 0 = (r : ℂ) := by
  simp [chosenPowerSum]

theorem imageHomogeneousMap_apply (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) (j : Fin D) :
    imageHomogeneousMap D r hD u j =
      chosenPivot r * u 0 ^ (D-(retainedIndex D hD j).val) *
        u 1 ^ (retainedIndex D hD j).val -
      chosenPowerSum r (retainedIndex D hD j).val * u 0 ^ (D-1) * u 1 := by
  simp [imageHomogeneousMap, imageHomogeneousCoordinate]

theorem imageHomogeneousMap_zero (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) :
    imageHomogeneousMap D r hD u (imageZeroIndex D hD) =
      chosenPivot r * u 0 ^ D - (r : ℂ) * (u 0 ^ (D-1) * u 1) := by
  rw [imageHomogeneousMap_apply]
  simp
  ring

theorem imageHomogeneousMap_two (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) :
    imageHomogeneousMap D r hD u (imageTwoIndex D hD) =
      chosenPivot r * (u 0 ^ (D-2) * u 1 ^ 2) -
        chosenPowerSum r 2 * (u 0 ^ (D-1) * u 1) := by
  rw [imageHomogeneousMap_apply]
  simp
  ring

theorem imageHomogeneousMap_last (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) :
    imageHomogeneousMap D r hD u (imageLastIndex D hD) =
      chosenPivot r * u 1 ^ D - chosenPowerSum r D * (u 0 ^ (D-1) * u 1) := by
  rw [imageHomogeneousMap_apply]
  simp
  ring

theorem imageHomogeneousMap_quadratic (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) :
    chosenPivot r * (chosenPivot r^2 - (r : ℂ)*chosenPowerSum r 2) * (u 0^D)^2 +
      (((r : ℂ)*chosenPowerSum r 2 - 2*chosenPivot r^2)*
        imageHomogeneousMap D r hD u (imageZeroIndex D hD) -
        (r : ℂ)^2*imageHomogeneousMap D r hD u (imageTwoIndex D hD)) * u 0^D +
      chosenPivot r * (imageHomogeneousMap D r hD u (imageZeroIndex D hD))^2 = 0 := by
  rw [imageHomogeneousMap_zero, imageHomogeneousMap_two]
  exact quotient_quadratic_identity _ _ _ _ _ _ (homogeneous_monomial_identity hD _ _)

theorem eval_imageSubstitution (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ)
    (p : ImageCoordinatePolynomial D) :
    MvPolynomial.eval u (imageSubstitution D r hD p) =
      MvPolynomial.eval (imageHomogeneousMap D r hD u) p := by
  exact MvPolynomial.comp_aeval_apply (imageHomogeneousCoordinate D r hD)
    (MvPolynomial.aeval u) p

theorem imageHomogeneousMap_finite (D r : ℕ) (hD : 2 ≤ D) (t : ℂ) :
    imageHomogeneousMap D r hD (![1,t]) = coordinateCurve D r hD (some t) := by
  ext j
  simp [imageHomogeneousMap_apply, coordinateCurve, coordinateProjection,
    curveVector, pivotIndex]

#print axioms imageHomogeneousMap_quadratic
end NLA.TR27.Paper
