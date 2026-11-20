module

public import NLA.TR27.PaperTangent
public import NLA.TR27.PaperProjectionDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization Classical
open Polynomial
namespace NLA.TR27.Paper

theorem separating_polynomial_annihilates {D k : ℕ} (hk : k < D)
    (t : Fin k → Option ℂ) (i j : Fin k) (hji : j ≠ i) :
    coefficientPairing D (separatingPolynomial t i) (curveVector D (t j)) = 0 := by
  cases hj : t j with
  | none =>
      rw [coefficientPairing_infinity]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (separatingPolynomial_degree t i) hk)
  | some a =>
      rw [coefficientPairing_finite _ _ ((separatingPolynomial_degree t i).trans hk.le)]
      exact separatingPolynomial_eval_other t i j hji a hj

/-- Uniform independence before projection, including the infinity parameter. -/
theorem curve_vectors_independent {D k : ℕ} (hk : k < D) (t : Fin k → Option ℂ)
    (ht : Function.Injective t) : LinearIndependent ℂ (fun i => curveVector D (t i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hfinite : ∀ i b, t i = some b → a i = 0 := by
    intro i b hib
    have hpair := congrArg (coefficientPairing D (separatingPolynomial t i)) ha
    simp only [map_sum, map_smul, map_zero] at hpair
    have hsum :
        (∑ j, a j • coefficientPairing D (separatingPolynomial t i) (curveVector D (t j))) =
        a i • coefficientPairing D (separatingPolynomial t i) (curveVector D (t i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        rw [separating_polynomial_annihilates hk t i j hji, smul_zero]
      · simp
    rw [hsum, hib, coefficientPairing_finite _ _
      ((separatingPolynomial_degree t i).trans hk.le)] at hpair
    exact (mul_eq_zero.mp hpair).resolve_right (separatingPolynomial_eval_self t ht i b hib)
  intro i
  cases hi : t i with
  | some b => exact hfinite i b hi
  | none =>
      have hsum : (∑ j, a j • curveVector D (t j)) = a i • curveVector D (t i) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          cases hj : t j with
          | none => exact (hji (ht (hj.trans hi.symm))).elim
          | some b => rw [hfinite j b hj, zero_smul]
        · simp
      have hzero : a i • curveVector D none = 0 := by simpa [hi] using hsum.symm.trans ha
      have hlast := congrFun hzero (Fin.last D)
      simpa [curveVector] using hlast

theorem tangent_not_short_span {D k : ℕ} (hD : 1 ≤ D) (hk : k < D)
    (t : Fin k → Option ℂ) :
    tangentVector D ∉ Submodule.span ℂ (Set.range (fun i => curveVector D (t i))) := by
  intro h
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  exact tangent_not_short_sum hD hk t a ha.symm

theorem center_not_short_span {D r k : ℕ} (hD : 1 ≤ D) (hk : k + r < D)
    (a : Fin r → Option ℂ) (t : Fin k → Option ℂ) :
    projectionCenter D r a ∉ Submodule.span ℂ (Set.range (fun i => curveVector D (t i))) := by
  classical
  intro hc
  let u : Fin (k+r) → Option ℂ := Fin.append t a
  let S := Submodule.span ℂ (Set.range (fun i => curveVector D (u i)))
  have ht : Submodule.span ℂ (Set.range (fun i => curveVector D (t i))) ≤ S := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Fin.castAdd r i, by simp [u]⟩
  have ha (i : Fin r) : curveVector D (a i) ∈ S := by
    exact Submodule.subset_span ⟨Fin.natAdd k i, by simp [u]⟩
  have he : tangentVector D = projectionCenter D r a + ∑ i, curveVector D (a i) := by
    simp [projectionCenter]
  apply tangent_not_short_span hD hk u
  rw [he]
  exact S.add_mem (ht hc) (S.sum_mem (fun i _ => ha i))

/-- Every small distinct parameter family remains independent under any
linear quotient with the paper's exact centre as its kernel. -/
theorem projected_curve_vectors_independent
    {V : Type*} [AddCommGroup V] [Module ℂ V] {D r k : ℕ}
    (hD : 1 ≤ D) (hk : k + r < D) (a : Fin r → Option ℂ)
    (P : CurveSpace D →ₗ[ℂ] V)
    (hker : LinearMap.ker P = Submodule.span ℂ {projectionCenter D r a})
    (t : Fin k → Option ℂ) (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i => P (curveVector D (t i))) := by
  have hd : Disjoint (Submodule.span ℂ (Set.range (fun i => curveVector D (t i))))
      (LinearMap.ker P) := by
    rw [hker]
    exact Submodule.disjoint_span_singleton_of_notMem (center_not_short_span hD hk a t)
  exact (P.linearIndependent_iff_of_disjoint hd).mpr (curve_vectors_independent (by omega) t ht)

#print axioms projected_curve_vectors_independent
end NLA.TR27.Paper
