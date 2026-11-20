module

public import NLA.TR27.PaperIntegralImage

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

theorem imageHomogeneousMap_infinity (D r : ℕ) (hD : 2 ≤ D) :
    imageHomogeneousMap D r hD (![0,1]) = coordinateCurve D r hD none := by
  ext j
  have h1 : D-1 ≠ 0 := by omega
  have hD1 : D ≠ 1 := by omega
  have hij : (retainedIndex D hD j).val ≤ D := by omega
  by_cases hi : (retainedIndex D hD j).val = D
  · simp [imageHomogeneousMap_apply, coordinateCurve, coordinateProjection,
      curveVector, pivotIndex, hi, h1, hD1, Ne.symm hD1]
  · have hn : D-(retainedIndex D hD j).val ≠ 0 := by omega
    simp [imageHomogeneousMap_apply, coordinateCurve, coordinateProjection,
      curveVector, pivotIndex, hi, h1, hn, hD1, Ne.symm hD1]

theorem imageHomogeneousMap_smul (D r : ℕ) (hD : 2 ≤ D) (a : ℂ) (u : Fin 2 → ℂ) :
    imageHomogeneousMap D r hD (a • u) = a^D • imageHomogeneousMap D r hD u := by
  ext j
  have hij : (retainedIndex D hD j).val ≤ D := by omega
  have ha : a^(D-(retainedIndex D hD j).val) * a^(retainedIndex D hD j).val = a^D := by
    rw [← pow_add, Nat.sub_add_cancel hij]
  have hb : a^(D-1)*a = a^D := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ D)]
  simp only [imageHomogeneousMap_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  calc
    _ = (a^(D-(retainedIndex D hD j).val)*a^(retainedIndex D hD j).val) *
        (chosenPivot r * u 0^(D-(retainedIndex D hD j).val) * u 1^(retainedIndex D hD j).val) -
        (a^(D-1)*a) * (chosenPowerSum r (retainedIndex D hD j).val*u 0^(D-1)*u 1) := by ring
    _ = _ := by rw [ha, hb]; ring

theorem image_range_eq_parameterizedCone (D r : ℕ) (hD : 2 ≤ D) :
    Set.range (imageHomogeneousMap D r hD) = coordinateParameterizedCone D r hD := by
  apply Set.Subset.antisymm
  · rintro w ⟨u, rfl⟩
    by_cases h0 : u 0 = 0
    · have hu : u = u 1 • (![0,1] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, h0]
      rw [hu, imageHomogeneousMap_smul, imageHomogeneousMap_infinity]
      by_cases h1 : u 1 = 0
      · left
        simp [h1, show D ≠ 0 by omega]
      · right
        exact ⟨u 1^D, pow_ne_zero _ h1, none, rfl⟩
    · have hu : u = u 0 • (![1,u 1/u 0] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [hu, imageHomogeneousMap_smul, imageHomogeneousMap_finite]
      right
      exact ⟨u 0^D, pow_ne_zero _ h0, some (u 1/u 0), rfl⟩
  · rintro w (rfl | ⟨a, ha, t, rfl⟩)
    · refine ⟨(0 : ℂ) • (![0,1] : Fin 2 → ℂ), ?_⟩
      rw [imageHomogeneousMap_smul]
      simp [show D ≠ 0 by omega]
    · obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (by omega : 0 < D)
      cases t with
      | none =>
        refine ⟨b • (![0,1] : Fin 2 → ℂ), ?_⟩
        rw [imageHomogeneousMap_smul, hb, imageHomogeneousMap_infinity]
      | some t =>
        refine ⟨b • (![1,t] : Fin 2 → ℂ), ?_⟩
        rw [imageHomogeneousMap_smul, hb, imageHomogeneousMap_finite]

theorem image_whole_closed_cone (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    MvPolynomial.zeroLocus ℂ (imageIdeal D r hD) = coordinateParameterizedCone D r hD :=
  (image_zeroLocus_eq_range D r hD hr).trans (image_range_eq_parameterizedCone D r hD)

theorem quotient_whole_closed_cone (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    (quotientCoordinateEquiv D r hD hr) ⁻¹' MvPolynomial.zeroLocus ℂ (imageIdeal D r hD) =
      quotientParameterizedCone D r := by
  rw [image_whole_closed_cone D r hD hr]
  ext w
  change (_ = 0 ∨ ∃ a : ℂ, a ≠ 0 ∧ ∃ t : Option ℂ,
      quotientCoordinateEquiv D r hD hr w = a • coordinateCurve D r hD t) ↔
    (w = 0 ∨ ∃ a : ℂ, a ≠ 0 ∧ ∃ t : Option ℂ,
      w = a • quotientCurve D r (chosenParameters r) t)
  have hc (t : Option ℂ) :
      quotientCoordinateEquiv D r hD hr (quotientCurve D r (chosenParameters r) t) =
        coordinateCurve D r hD t := quotientCoordinateEquiv_projection D r hD hr _
  constructor
  · rintro (h | ⟨a, ha, t, ht⟩)
    · exact Or.inl ((quotientCoordinateEquiv D r hD hr).map_eq_zero_iff.mp h)
    · right
      refine ⟨a, ha, t, (quotientCoordinateEquiv D r hD hr).injective ?_⟩
      simpa only [map_smul, hc] using ht
  · rintro (rfl | ⟨a, ha, t, rfl⟩)
    · exact Or.inl (map_zero _)
    · exact Or.inr ⟨a, ha, t, by rw [map_smul, hc]⟩

#print axioms quotient_whole_closed_cone
end NLA.TR27.Paper
