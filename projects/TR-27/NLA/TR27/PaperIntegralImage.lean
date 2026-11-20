module

public import NLA.TR27.PaperHomogeneous
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

variable (D r : ℕ) (hD : 2 ≤ D)

abbrev imageAlgebra : Algebra (ImageCoordinatePolynomial D) CurveParameterPolynomial :=
  (imageSubstitution D r hD : ImageCoordinatePolynomial D →+* CurveParameterPolynomial).toAlgebra

theorem image_algebraMap :
    letI := imageAlgebra D r hD
    algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial =
      (imageSubstitution D r hD : ImageCoordinatePolynomial D →+* CurveParameterPolynomial) := rfl

theorem image_integral_constant (c : ℂ) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D) (MvPolynomial.C c : CurveParameterPolynomial) := by
  letI := imageAlgebra D r hD
  simpa [image_algebraMap, imageSubstitution] using
    (isIntegral_algebraMap (R := ImageCoordinatePolynomial D) (A := CurveParameterPolynomial)
      (x := MvPolynomial.C c))

theorem image_integral_coordinate (j : Fin D) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D) (imageHomogeneousCoordinate D r hD j) := by
  letI := imageAlgebra D r hD
  simpa [image_algebraMap, imageSubstitution] using
    (isIntegral_algebraMap (R := ImageCoordinatePolynomial D) (A := CurveParameterPolynomial)
      (x := MvPolynomial.X j))

theorem image_parameter_zero_power_integral (hr : 3 ≤ r) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D)
      ((MvPolynomial.X (0 : Fin 2) : CurveParameterPolynomial)^D) := by
  letI := imageAlgebra D r hD
  let L : ℂ := chosenPivot r * (chosenPivot r^2 - (r : ℂ)*chosenPowerSum r 2)
  let A : ImageCoordinatePolynomial D := MvPolynomial.C L⁻¹ *
    (MvPolynomial.C ((r : ℂ)*chosenPowerSum r 2 - 2*chosenPivot r^2) *
      MvPolynomial.X (imageZeroIndex D hD) -
      MvPolynomial.C ((r : ℂ)^2) * MvPolynomial.X (imageTwoIndex D hD))
  let B : ImageCoordinatePolynomial D :=
    MvPolynomial.C L⁻¹ * MvPolynomial.C (chosenPivot r) *
      MvPolynomial.X (imageZeroIndex D hD)^2
  refine ⟨Polynomial.X^2 + (Polynomial.C A * Polynomial.X + Polynomial.C B), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree
    norm_num
  · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [image_algebraMap]
    apply MvPolynomial.funext
    intro u
    simp only [map_add, map_mul, map_pow, map_zero, MvPolynomial.eval_X]
    change (u 0^D)^2 +
      (MvPolynomial.eval u (imageSubstitution D r hD A) * u 0^D +
        MvPolynomial.eval u (imageSubstitution D r hD B)) = 0
    rw [eval_imageSubstitution, eval_imageSubstitution]
    simp only [A, B, map_mul, map_sub, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
    have hL : L ≠ 0 := quadratic_leading_coefficient_ne_zero hr
    have h := imageHomogeneousMap_quadratic D r hD u
    change L * (u 0^D)^2 + _ + _ = 0 at h
    field_simp [hL]
    linear_combination h

theorem image_parameter_mixed_integral (hr : 3 ≤ r) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D)
      ((MvPolynomial.X (0 : Fin 2) : CurveParameterPolynomial)^(D-1) * MvPolynomial.X 1) := by
  letI := imageAlgebra D r hD
  have h := (image_integral_constant D r hD (1/(r : ℂ))).mul
    (((image_integral_constant D r hD (chosenPivot r)).mul
      (image_parameter_zero_power_integral D r hD hr)).sub
        (image_integral_coordinate D r hD (imageZeroIndex D hD)))
  convert h using 1 <;> try rfl
  apply MvPolynomial.funext
  intro u
  simp only [map_mul, map_sub, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
  change u 0^(D-1) * u 1 = (1/(r : ℂ)) *
    (chosenPivot r * u 0^D - imageHomogeneousMap D r hD u (imageZeroIndex D hD))
  rw [imageHomogeneousMap_zero]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

theorem image_parameter_one_power_integral (hr : 3 ≤ r) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D)
      ((MvPolynomial.X (1 : Fin 2) : CurveParameterPolynomial)^D) := by
  letI := imageAlgebra D r hD
  have h := (image_integral_constant D r hD (1/chosenPivot r)).mul
    ((image_integral_coordinate D r hD (imageLastIndex D hD)).add
      ((image_integral_constant D r hD (chosenPowerSum r D)).mul
        (image_parameter_mixed_integral D r hD hr)))
  convert h using 1 <;> try rfl
  apply MvPolynomial.funext
  intro u
  simp only [map_mul, map_add, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
  change u 1^D = (1/chosenPivot r) *
    (imageHomogeneousMap D r hD u (imageLastIndex D hD) +
      chosenPowerSum r D * (u 0^(D-1)*u 1))
  rw [imageHomogeneousMap_last]
  have hb := chosenPivot_ne_zero hr
  field_simp
  ring

theorem image_parameter_integral (hr : 3 ≤ r) (j : Fin 2) :
    letI := imageAlgebra D r hD
    IsIntegral (ImageCoordinatePolynomial D) (MvPolynomial.X j : CurveParameterPolynomial) := by
  letI := imageAlgebra D r hD
  fin_cases j
  · exact IsIntegral.of_pow (by omega : 0 < D) (image_parameter_zero_power_integral D r hD hr)
  · exact IsIntegral.of_pow (by omega : 0 < D) (image_parameter_one_power_integral D r hD hr)

theorem image_substitution_integral (hr : 3 ≤ r) :
    (imageSubstitution D r hD : ImageCoordinatePolynomial D →+* CurveParameterPolynomial).IsIntegral := by
  letI := imageAlgebra D r hD
  intro p
  change IsIntegral (ImageCoordinatePolynomial D) p
  induction p using MvPolynomial.induction_on with
  | C c => exact image_integral_constant D r hD c
  | add p q hp hq => exact hp.add hq
  | mul_X p j hp => exact hp.mul (image_parameter_integral D r hD hr j)

theorem imageHomogeneousMap_mem_zeroLocus (u : Fin 2 → ℂ) :
    imageHomogeneousMap D r hD u ∈ MvPolynomial.zeroLocus ℂ (imageIdeal D r hD) := by
  intro p hp
  change imageSubstitution D r hD p = 0 at hp
  change MvPolynomial.eval (imageHomogeneousMap D r hD u) p = 0
  rw [← eval_imageSubstitution, hp, map_zero]

theorem image_zeroLocus_eq_range (hr : 3 ≤ r) :
    MvPolynomial.zeroLocus ℂ (imageIdeal D r hD) = Set.range (imageHomogeneousMap D r hD) := by
  letI := imageAlgebra D r hD
  let : Algebra.IsIntegral (ImageCoordinatePolynomial D) CurveParameterPolynomial :=
    ⟨image_substitution_integral D r hD hr⟩
  apply Set.Subset.antisymm
  · intro w hw
    let M : Ideal (ImageCoordinatePolynomial D) := MvPolynomial.vanishingIdeal ℂ {w}
    have hM : M.IsMaximal := inferInstance
    have hker : RingHom.ker (algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial) ≤ M := by
      intro p hp
      change p ∈ imageIdeal D r hD at hp
      simpa only [M, MvPolynomial.mem_vanishingIdeal_iff, Set.mem_singleton_iff,
        forall_eq] using hw p hp
    obtain ⟨N, hN, hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral M hker
    obtain ⟨u, hu⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hN
    refine ⟨u, ?_⟩
    funext j
    have hj : MvPolynomial.X j - MvPolynomial.C (w j) ∈ M := by simp [M]
    rw [← hcomap] at hj
    change algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial
      (MvPolynomial.X j - MvPolynomial.C (w j)) ∈ N at hj
    rw [hu] at hj
    have heval := (MvPolynomial.mem_vanishingIdeal_iff.mp hj) u (Set.mem_singleton u)
    change MvPolynomial.eval u (imageSubstitution D r hD
      (MvPolynomial.X j - MvPolynomial.C (w j))) = 0 at heval
    rw [eval_imageSubstitution] at heval
    simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] using heval
  · rintro w ⟨u, rfl⟩
    exact imageHomogeneousMap_mem_zeroLocus D r hD u

#print axioms image_substitution_integral
#print axioms image_zeroLocus_eq_range
end NLA.TR27.Paper
