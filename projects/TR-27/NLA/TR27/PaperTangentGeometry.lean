module

public import NLA.TR27.PaperTangentGeometryDefinitions
public import NLA.TR27.PaperHankelRank
public import NLA.TR27.PaperQuotient
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem curveVector_hasDerivAt (D : ℕ) (a : ℂ) :
    HasDerivAt (fun t => curveVector D (some t)) (curveTangent D (some a)) a := by
  apply hasDerivAt_pi.mpr
  intro j
  exact hasDerivAt_pow j.val a

theorem infinityChart_zero (D : ℕ) : infinityChart D 0 = curveVector D none := by
  ext j
  have hj : j.val ≤ D := by omega
  by_cases h : j.val = D
  · simp [infinityChart, curveVector, h]
  · have hn : D-j.val ≠ 0 := by omega
    simp [infinityChart, curveVector, h, hn]

theorem infinityChart_hasDerivAt (D : ℕ) :
    HasDerivAt (infinityChart D) (curveTangent D none) 0 := by
  apply hasDerivAt_pi.mpr
  intro j
  have h := hasDerivAt_pow (D-j.val) (0 : ℂ)
  change HasDerivAt (fun t : ℂ => t^(D-j.val)) (if j.val+1 = D then 1 else 0) 0
  have hj : j.val ≤ D := by omega
  by_cases heq : j.val+1 = D
  · have h1 : D-j.val = 1 := by omega
    simpa [heq, h1] using h
  · by_cases hz : D-j.val = 0
    · simpa [heq, hz] using h
    · have hp : D-j.val-1 ≠ 0 := by omega
      simpa [heq, hp] using h

theorem power_derivative_product (i j : ℕ) (a : ℂ) :
    ((i+j : ℕ) : ℂ)*a^(i+j-1) =
      ((i : ℂ)*a^(i-1))*a^j + a^i*((j : ℂ)*a^(j-1)) := by
  by_cases hi : i = 0
  · subst i
    simp
  by_cases hj : j = 0
  · subst j
    simp
  have h1 : i-1+j = i+j-1 := by omega
  have h2 : i+(j-1) = i+j-1 := by omega
  rw [Nat.cast_add]
  calc
    _ = (i : ℂ)*a^(i-1+j) + (j : ℂ)*a^(i+(j-1)) := by rw [h1, h2]; ring
    _ = _ := by rw [pow_add, pow_add]; ring

theorem sourceHankel_tangent_rank {D n : ℕ} (hD : 2*n ≤ D) (a α β : ℂ) :
    (sourceHankel n hD (α • curveVector D (some a) + β • curveTangent D (some a))).rank ≤ 2 := by
  let U : Matrix (Fin (n+1)) (Fin 2) ℂ := Matrix.of fun i => ![a^i.val, (i.val : ℂ)*a^(i.val-1)]
  let V : Matrix (Fin 2) (Fin (n+1)) ℂ := Matrix.of fun l j =>
    (![α*a^j.val + β*((j.val : ℂ)*a^(j.val-1)), β*a^j.val] : Fin 2 → ℂ) l
  have heq : sourceHankel n hD (α • curveVector D (some a) + β • curveTangent D (some a)) = U*V := by
    ext i j
    change α*a^(i.val+j.val) + β*(((i.val+j.val : ℕ) : ℂ)*a^(i.val+j.val-1)) =
      ∑ l : Fin 2, U i l * V l j
    rw [power_derivative_product, pow_add]
    simp only [Fin.sum_univ_two, U, V, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    ring
  rw [heq]
  exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)

theorem center_not_finite_tangent {D r : ℕ} (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t α β : ℂ) :
    projectionCenter D r (fun i => some (a i)) ≠
      α • curveVector D (some t) + β • curveTangent D (some t) := by
  intro heq
  have hd : (sourceHankel (r+1) hD (projectionCenter D r (fun i => some (a i)))).det ≠ 0 := by
    rw [centerHankel_coordinates]
    exact centerHankel_det_ne_zero r a ha ha0
  rw [heq] at hd
  have hfull := Matrix.rank_of_det_ne_zero hd
  have hlow := sourceHankel_tangent_rank hD t α β
  simp only [Fintype.card_fin] at hfull
  omega

theorem center_not_infinity_tangent {D r : ℕ} (hr : 1 ≤ r) (hD : 2 ≤ D)
    (a : Fin r → ℂ) (α β : ℂ) :
    projectionCenter D r (fun i => some (a i)) ≠
      α • curveVector D none + β • curveTangent D none := by
  intro heq
  have h := congrFun heq ⟨0, by omega⟩
  have h0 : D ≠ 0 := by omega
  have h1 : D ≠ 1 := by omega
  simp [projectionCenter, tangentVector, curveVector, curveTangent, Finset.sum_apply,
    h0, h1, Ne.symm h0, Ne.symm h1] at h
  omega

theorem center_not_tangent {D r : ℕ} (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0)
    (t : Option ℂ) (α β : ℂ) :
    projectionCenter D r (fun i => some (a i)) ≠
      α • curveVector D t + β • curveTangent D t := by
  cases t with
  | none => exact center_not_infinity_tangent hr (by omega) a α β
  | some t => exact center_not_finite_tangent hr hD a ha ha0 t α β

theorem curve_tangent_coefficients_eq_zero {D : ℕ} (hD : 1 ≤ D)
    (t : Option ℂ) (α β : ℂ)
    (h : α • curveVector D t + β • curveTangent D t = 0) : α = 0 ∧ β = 0 := by
  cases t with
  | some a =>
    have hα := congrFun h ⟨0, by omega⟩
    have hβ := congrFun h ⟨1, by omega⟩
    simp [curveVector, curveTangent] at hα
    simp [curveVector, curveTangent, hα] at hβ
    exact ⟨hα, hβ⟩
  | none =>
    have hα := congrFun h ⟨D, by omega⟩
    have hβ := congrFun h ⟨D-1, by omega⟩
    have hne : D+1 ≠ D := by omega
    have hpre : D-1+1 = D := by omega
    have hpre' : D-1 ≠ D := by omega
    simp [curveVector, curveTangent, hne] at hα
    simp [curveVector, curveTangent, hpre, hpre'] at hβ
    exact ⟨hα, hβ⟩

theorem projected_curve_tangent_coefficients_eq_zero {D r : ℕ}
    (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : Option ℂ) (α β : ℂ)
    (h : α • quotientCurve D r (fun i => some (a i)) t +
      β • quotientProjection D r (fun i => some (a i)) (curveTangent D t) = 0) :
    α = 0 ∧ β = 0 := by
  let w := α • curveVector D t + β • curveTangent D t
  have hw : w ∈ LinearMap.ker (quotientProjection D r (fun i => some (a i))) := by
    rw [LinearMap.mem_ker]
    dsimp only [w]
    rw [map_add, map_smul, map_smul]
    exact h
  rw [quotientProjection_kernel, Submodule.mem_span_singleton] at hw
  obtain ⟨c, hc⟩ := hw
  by_cases hz : c = 0
  · have hw0 : w = 0 := by simpa only [hz, zero_smul] using hc.symm
    exact curve_tangent_coefficients_eq_zero (by omega) t α β hw0
  · exfalso
    apply center_not_tangent hr hD a ha ha0 t (c⁻¹*α) (c⁻¹*β)
    calc
      _ = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hz, one_smul]
      _ = _ := by simp only [w, smul_add, smul_smul]

#print axioms curveVector_hasDerivAt
#print axioms infinityChart_hasDerivAt
#print axioms center_not_finite_tangent
#print axioms center_not_infinity_tangent
#print axioms projected_curve_tangent_coefficients_eq_zero
end NLA.TR27.Paper
