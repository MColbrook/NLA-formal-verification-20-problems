module

public import NLA.TR27.PaperClosedImage
public import NLA.TR27.PaperQuotientSpan
public import NLA.TR27.ProjectiveGeometry
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper
attribute [local instance] MvPolynomial.gradedAlgebra

theorem imageHomogeneousCoordinate_isHomogeneous (D r : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    (imageHomogeneousCoordinate D r hD j).IsHomogeneous D := by
  unfold imageHomogeneousCoordinate
  apply MvPolynomial.IsHomogeneous.sub
  · have h := (MvPolynomial.isHomogeneous_C_mul_X_pow (chosenPivot r)
      (0 : Fin 2) (D-(retainedIndex D hD j).val)).mul
        (MvPolynomial.isHomogeneous_X_pow (1 : Fin 2) (retainedIndex D hD j).val)
    have hi : (retainedIndex D hD j).val ≤ D := by omega
    simpa [Nat.sub_add_cancel hi] using h
  · have h := (MvPolynomial.isHomogeneous_C_mul_X_pow
      (chosenPowerSum r (retainedIndex D hD j).val) (0 : Fin 2) (D-1)).mul
        (MvPolynomial.isHomogeneous_X (R := ℂ) (1 : Fin 2))
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ D)] using h

theorem imageHomogeneousMap_eq_zero_iff (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (u : Fin 2 → ℂ) : imageHomogeneousMap D r hD u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hq := imageHomogeneousMap_quadratic D r hD u
    rw [h] at hq
    simp only [Pi.zero_apply, mul_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero] at hq
    have hu0 : u 0 = 0 := eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp hq).resolve_left (quadratic_leading_coefficient_ne_zero hr)))
    have hl := congrFun h (imageLastIndex D hD)
    rw [imageHomogeneousMap_last] at hl
    simp only [Pi.zero_apply, hu0, zero_pow (by omega : D-1 ≠ 0), mul_zero, zero_mul,
      sub_zero] at hl
    have hu1 : u 1 = 0 := eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp hl).resolve_left (chosenPivot_ne_zero hr))
    ext j
    fin_cases j <;> simp [hu0, hu1]
  · rintro rfl
    have h := imageHomogeneousMap_smul D r hD (0 : ℂ) (0 : Fin 2 → ℂ)
    simpa [show D ≠ 0 by omega] using h

theorem imageSubstitution_homogeneous (D r : ℕ) (hD : 2 ≤ D)
    {p : ImageCoordinatePolynomial D} {n : ℕ} (hp : p.IsHomogeneous n) :
    (imageSubstitution D r hD p).IsHomogeneous (D*n) := by
  exact hp.aeval (imageHomogeneousCoordinate D r hD) (imageHomogeneousCoordinate_isHomogeneous D r hD)

theorem imageSubstitution_homogeneousComponent (D r : ℕ) (hD : 2 ≤ D)
    (p : ImageCoordinatePolynomial D) (n : ℕ) :
    MvPolynomial.homogeneousComponent (D*n) (imageSubstitution D r hD p) =
      imageSubstitution D r hD (MvPolynomial.homogeneousComponent n p) := by
  have hsum : imageSubstitution D r hD p =
      ∑ i ∈ Finset.range (p.totalDegree+1),
        imageSubstitution D r hD (MvPolynomial.homogeneousComponent i p) := by
    rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
  rw [hsum, map_sum]
  simp_rw [MvPolynomial.homogeneousComponent_of_mem
    (imageSubstitution_homogeneous D r hD (MvPolynomial.homogeneousComponent_isHomogeneous _ _))]
  simp only [Nat.mul_left_cancel_iff (by omega : 0 < D)]
  by_cases hn : n < p.totalDegree+1
  · simp [hn]
  · have hp : p.totalDegree < n := by omega
    simp [hn, MvPolynomial.homogeneousComponent_eq_zero n p hp]

theorem imageIdeal_isHomogeneous (D r : ℕ) (hD : 2 ≤ D) :
    (imageIdeal D r hD).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin D) ℂ) := by
  intro n p hp
  rw [← DirectSum.Decomposition.decompose'_eq, MvPolynomial.decomposition.decompose'_apply]
  change imageSubstitution D r hD (MvPolynomial.homogeneousComponent n p) = 0
  change imageSubstitution D r hD p = 0 at hp
  rw [← imageSubstitution_homogeneousComponent, hp, map_zero]

theorem imageIdeal_isPrime (D r : ℕ) (hD : 2 ≤ D) : (imageIdeal D r hD).IsPrime :=
  RingHom.ker_isPrime (imageSubstitution D r hD : ImageCoordinatePolynomial D →+* CurveParameterPolynomial)

theorem quotient_image_admissible (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    (ProjectiveVariety.mk D (quotientCoordinateEquiv D r hD hr) (imageIdeal D r hD)).Admissible := by
  let X := ProjectiveVariety.mk D (quotientCoordinateEquiv D r hD hr) (imageIdeal D r hD)
  have hc : X.cone = quotientParameterizedCone D r := quotient_whole_closed_cone D r hD hr
  letI : (imageIdeal D r hD).IsPrime := imageIdeal_isPrime D r hD
  refine ⟨imageIdeal_isHomogeneous D r hD, imageIdeal_isPrime D r hD, ?_, ?_, ?_⟩
  · change IsReduced (ImageCoordinatePolynomial D ⧸ imageIdeal D r hD)
    infer_instance
  · refine ⟨quotientCurve D r (chosenParameters r) (some 0), ?_, ?_⟩
    · change _ ∈ X.cone
      rw [hc]
      exact Or.inr ⟨1, one_ne_zero, some 0, (one_smul _ _).symm⟩
    · intro hz
      have he := congrArg (quotientCoordinateEquiv D r hD hr) hz
      rw [quotientCurve, quotientCoordinateEquiv_projection, map_zero] at he
      change coordinateCurve D r hD (some 0) = 0 at he
      rw [← imageHomogeneousMap_finite] at he
      have hu := (imageHomogeneousMap_eq_zero_iff D r hD hr _).mp he
      have := congrFun hu 0
      simpa using this
  · change Submodule.span ℂ X.cone = ⊤
    rw [hc]
    apply top_unique
    rw [← quotient_curve_span D r (chosenParameters r)]
    apply Submodule.span_mono
    rintro w ⟨t, rfl⟩
    exact Or.inr ⟨1, one_ne_zero, t, (one_smul _ _).symm⟩

theorem quotient_image_points (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    (ProjectiveVariety.mk D (quotientCoordinateEquiv D r hD hr) (imageIdeal D r hD)).points =
      quotientPoints D r (chosenParameters r) := by
  ext p
  change p.rep ∈ (ProjectiveVariety.mk D (quotientCoordinateEquiv D r hD hr)
    (imageIdeal D r hD)).cone ↔ _
  change p.rep ∈ (quotientCoordinateEquiv D r hD hr) ⁻¹'
    MvPolynomial.zeroLocus ℂ (imageIdeal D r hD) ↔ _
  rw [quotient_whole_closed_cone D r hD hr]
  constructor
  · rintro (hz | ⟨a, ha, t, ht⟩)
    · exact (p.rep_nonzero hz).elim
    · exact ⟨t, a, ha, ht⟩
  · rintro ⟨t, a, ha, ht⟩
    exact Or.inr ⟨a, ha, t, ht⟩

#print axioms quotient_image_admissible
#print axioms quotient_image_points
end NLA.TR27.Paper
