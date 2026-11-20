module

public import NLA.TR27.ArbitraryCoordinates
public import NLA.TR27.PaperClosedImage

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem parameterHomogeneousMap_apply (D r : ℕ) (a : Fin r → ℂ)
    (u : Fin 2 → ℂ) (j : Fin D) :
    parameterHomogeneousMap D r a u j =
      (r : ℂ)*u 0^(D-j.succ.val)*u 1^j.succ.val +
        projectionCenter D r (fun i => some (a i)) j.succ*u 0^D := by
  simp [parameterHomogeneousMap, parameterHomogeneousCoordinate]

theorem parameterHomogeneousMap_finite (D r : ℕ) (a : Fin r → ℂ) (t : ℂ) :
    parameterHomogeneousMap D r a (![1,t]) = parameterCoordinateCurve D r a (some t) := by
  ext j
  simp [parameterHomogeneousMap_apply, parameterCoordinateCurve, parameterProjection, curveVector]

theorem parameterHomogeneousMap_infinity (D r : ℕ) (hD : 1 ≤ D) (a : Fin r → ℂ) :
    parameterHomogeneousMap D r a (![0,1]) = parameterCoordinateCurve D r a none := by
  ext j
  have hj : j.succ.val ≤ D := by omega
  have hD0 : D ≠ 0 := by omega
  by_cases he : j.val+1 = D
  · simp [parameterHomogeneousMap_apply, parameterCoordinateCurve, parameterProjection,
      curveVector, he, hD0, Ne.symm hD0]
  · have hne : D-(j.val+1) ≠ 0 := by omega
    simp [parameterHomogeneousMap_apply, parameterCoordinateCurve, parameterProjection,
      curveVector, he, hne, hD0, Ne.symm hD0]

theorem parameterHomogeneousMap_smul (D r : ℕ) (a : Fin r → ℂ)
    (c : ℂ) (u : Fin 2 → ℂ) :
    parameterHomogeneousMap D r a (c • u) = c^D • parameterHomogeneousMap D r a u := by
  ext j
  have hj : j.succ.val ≤ D := by omega
  have hc : c^(D-j.succ.val)*c^j.succ.val = c^D := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  simp only [parameterHomogeneousMap_apply, Pi.smul_apply, smul_eq_mul, mul_pow]
  calc
    _ = (c^(D-j.succ.val)*c^j.succ.val) *
        ((r : ℂ)*u 0^(D-j.succ.val)*u 1^j.succ.val) +
        c^D*(projectionCenter D r (fun i => some (a i)) j.succ*u 0^D) := by ring
    _ = _ := by rw [hc]; ring

theorem parameterHomogeneousMap_eq_zero_iff (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (u : Fin 2 → ℂ) :
    parameterHomogeneousMap D r a u = 0 ↔ u = 0 := by
  constructor
  · intro hz
    by_contra hne
    by_cases h0 : u 0 = 0
    · have h1 : u 1 ≠ 0 := by
        intro h1
        apply hne
        ext j
        fin_cases j <;> simp [h0,h1]
      have he : u = u 1 • (![0,1] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul, h0]
      rw [he, parameterHomogeneousMap_smul, parameterHomogeneousMap_infinity D r hD a] at hz
      exact (smul_ne_zero (pow_ne_zero _ h1)
        (parameterCoordinateCurve_nonzero D r hD hr hgap a none)) hz
    · have he : u = u 0 • (![1,u 1/u 0] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [he, parameterHomogeneousMap_smul, parameterHomogeneousMap_finite] at hz
      exact (smul_ne_zero (pow_ne_zero _ h0)
        (parameterCoordinateCurve_nonzero D r hD hr hgap a (some (u 1/u 0)))) hz
  · rintro rfl
    ext j
    simp [parameterHomogeneousMap_apply, show D ≠ 0 by omega]

/-- Some moment supplies a monic integral relation. If none did, the centre
would itself lie on the rational normal curve, contrary to its rank bound. -/
theorem parameter_integral_moment (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) :
    ∃ j : Fin D, 2 ≤ j.succ.val ∧
      (-projectionCenter D r (fun i => some (a i)) ⟨1,by omega⟩)^j.succ.val +
        (r : ℂ)^(j.succ.val-1)*projectionCenter D r (fun i => some (a i)) j.succ ≠ 0 := by
  let z := projectionCenter D r (fun i => some (a i))
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  by_contra h
  push Not at h
  have he : z = -(r : ℂ) • curveVector D (some (-z ⟨1,by omega⟩/(r : ℂ))) := by
    ext i
    have hi : i.val ≤ D := by omega
    change z i = -(r : ℂ)*(-z ⟨1,by omega⟩/(r : ℂ))^i.val
    by_cases h0 : i.val = 0
    · have hi0 : i = 0 := Fin.ext h0
      subst i
      simp [z, parameter_center_zero]
    by_cases h1 : i.val = 1
    · have hi1 : i = (⟨1,by omega⟩ : Fin (D+1)) := Fin.ext h1
      simp only [h1,pow_one,hi1]
      field_simp [hr0]
      <;> ring
    have hi2 : 2 ≤ i.val := by omega
    let j : Fin D := ⟨i.val-1, by omega⟩
    have hji : j.succ = i := Fin.ext (by dsimp [j]; omega)
    have hm := h j (by dsimp [j]; omega)
    rw [hji] at hm
    change (-z ⟨1,by omega⟩)^i.val+(r : ℂ)^(i.val-1)*z i = 0 at hm
    rw [div_pow, ← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero i.val hr0)).mpr
    have hp : (r : ℂ)^i.val = (r : ℂ)^(i.val-1)*(r : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ i.val)]
    rw [hp]
    linear_combination (r : ℂ)*hm
  apply center_not_short_span hD hgap (fun i => some (a i))
    (fun _ : Fin 1 => some (-z ⟨1,by omega⟩/(r : ℂ)))
  let S := Submodule.span ℂ (Set.range (fun _ : Fin 1 =>
    curveVector D (some (-z ⟨1,by omega⟩/(r : ℂ)))))
  have hc : curveVector D (some (-z ⟨1,by omega⟩/(r : ℂ))) ∈ S :=
    Submodule.subset_span ⟨0,rfl⟩
  have hm := S.smul_mem (-(r : ℂ)) hc
  rw [← he] at hm
  exact hm

end NLA.TR27.Paper
